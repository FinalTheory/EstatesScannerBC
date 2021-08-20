# -*- coding: utf-8 -*-
import signal
import sys
import os
import requests
import pytz
import pickle
import js2py
from datetime import timedelta, datetime, date
from time import sleep
from collections import namedtuple
from bs4 import BeautifulSoup
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.image import MIMEImage
import time
import base64
import itertools
import matplotlib.pyplot as plt
import numpy as np
from dateutil import parser
from matplotlib.ticker import FuncFormatter

EMAIL_LIST = ["finaltheory@hotmail.com", "dingfengqin@sohu.com"]
EXCLUDE_CITY = ["Abbotsford", "Chilliwack", "Langley", "Mission", "unknown"]

BC_ASSESSMENT_TIMEOUT = 2

# days
ESTATE_SLA = 3
GOOD_PRICE_UPPER_THRESHOLD = 0.12
GOOD_PRICE_LOWER_THRESHOLD = -0.1

SoldEstateSet = dict()
EstateSet = dict()

SALE_FILE_NAME = 'estate.pickle'
SOLD_FILE_NAME = 'sold_estate.pickle'

JS_FUNC = """
var gReceiver_ = function(n) {
    function t(n, t) {
        return n << t | n >>> 32 - t
    }
    function r(n, t) {
        var r, e, o, i, u;
        return o = 2147483648 & n,
        i = 2147483648 & t,
        u = (1073741823 & n) + (1073741823 & t),
        (r = 1073741824 & n) & (e = 1073741824 & t) ? 2147483648 ^ u ^ o ^ i : r | e ? 1073741824 & u ? 3221225472 ^ u ^ o ^ i : 1073741824 ^ u ^ o ^ i : u ^ o ^ i
    }
    function e(n, e, o, i, u, f, c) {
        return n = r(n, r(r(function(n, t, r) {
            return n & t | ~n & r
        }(e, o, i), u), c)),
        r(t(n, f), e)
    }
    function o(n, e, o, i, u, f, c) {
        return n = r(n, r(r(function(n, t, r) {
            return n & r | t & ~r
        }(e, o, i), u), c)),
        r(t(n, f), e)
    }
    function i(n, e, o, i, u, f, c) {
        return n = r(n, r(r(function(n, t, r) {
            return n ^ t ^ r
        }(e, o, i), u), c)),
        r(t(n, f), e)
    }
    function u(n, e, o, i, u, f, c) {
        return n = r(n, r(r(function(n, t, r) {
            return t ^ (n | ~r)
        }(e, o, i), u), c)),
        r(t(n, f), e)
    }
    function f(n) {
        var t, r = "", e = "";
        for (t = 0; t <= 3; t++)
            r += (e = "0" + (n >>> 8 * t & 255).toString(16)).substr(e.length - 2, 2);
        return r
    }
    var c, l, s, a, h, p, v, d, g, m = Array();
    for (m = function(n) {
        for (var t, r = n.length, e = r + 8, o = 16 * ((e - e % 64) / 64 + 1), i = Array(o - 1), u = 0, f = 0; f < r; )
            u = f % 4 * 8,
            i[t = (f - f % 4) / 4] = i[t] | n.charCodeAt(f) << u,
            f++;
        return u = f % 4 * 8,
        i[t = (f - f % 4) / 4] = i[t] | 128 << u,
        i[o - 2] = r << 3,
        i[o - 1] = r >>> 29,
        i
    }(n = function(n) {
        for (var t = "", r = 0; r < n.length; r++) {
            var e = n.charCodeAt(r);
            e < 128 ? t += String.fromCharCode(e) : e > 127 && e < 2048 ? (t += String.fromCharCode(e >> 6 | 192),
            t += String.fromCharCode(63 & e | 128)) : (t += String.fromCharCode(e >> 12 | 224),
            t += String.fromCharCode(e >> 6 & 63 | 128),
            t += String.fromCharCode(63 & e | 128))
        }
        return t
    }(n)),
    p = 1732584193,
    v = 4023233417,
    d = 2562383102,
    g = 271733878,
    c = 0; c < m.length; c += 16)
        l = p,
        s = v,
        a = d,
        h = g,
        p = e(p, v, d, g, m[c + 0], 7, 3614090360),
        g = e(g, p, v, d, m[c + 1], 12, 3905402710),
        d = e(d, g, p, v, m[c + 2], 17, 606105819),
        v = e(v, d, g, p, m[c + 3], 22, 3250441966),
        p = e(p, v, d, g, m[c + 4], 7, 4118548399),
        g = e(g, p, v, d, m[c + 5], 12, 1200080426),
        d = e(d, g, p, v, m[c + 6], 17, 2821735955),
        v = e(v, d, g, p, m[c + 7], 22, 4249261313),
        p = e(p, v, d, g, m[c + 8], 7, 1770035416),
        g = e(g, p, v, d, m[c + 9], 12, 2336552879),
        d = e(d, g, p, v, m[c + 10], 17, 4294925233),
        v = e(v, d, g, p, m[c + 11], 22, 2304563134),
        p = e(p, v, d, g, m[c + 12], 7, 1804603682),
        g = e(g, p, v, d, m[c + 13], 12, 4254626195),
        d = e(d, g, p, v, m[c + 14], 17, 2792965006),
        p = o(p, v = e(v, d, g, p, m[c + 15], 22, 1236535329), d, g, m[c + 1], 5, 4129170786),
        g = o(g, p, v, d, m[c + 6], 9, 3225465664),
        d = o(d, g, p, v, m[c + 11], 14, 643717713),
        v = o(v, d, g, p, m[c + 0], 20, 3921069994),
        p = o(p, v, d, g, m[c + 5], 5, 3593408605),
        g = o(g, p, v, d, m[c + 10], 9, 38016083),
        d = o(d, g, p, v, m[c + 15], 14, 3634488961),
        v = o(v, d, g, p, m[c + 4], 20, 3889429448),
        p = o(p, v, d, g, m[c + 9], 5, 568446438),
        g = o(g, p, v, d, m[c + 14], 9, 3275163606),
        d = o(d, g, p, v, m[c + 3], 14, 4107603335),
        v = o(v, d, g, p, m[c + 8], 20, 1163531501),
        p = o(p, v, d, g, m[c + 13], 5, 2850285829),
        g = o(g, p, v, d, m[c + 2], 9, 4243563512),
        d = o(d, g, p, v, m[c + 7], 14, 1735328473),
        p = i(p, v = o(v, d, g, p, m[c + 12], 20, 2368359562), d, g, m[c + 5], 4, 4294588738),
        g = i(g, p, v, d, m[c + 8], 11, 2272392833),
        d = i(d, g, p, v, m[c + 11], 16, 1839030562),
        v = i(v, d, g, p, m[c + 14], 23, 4259657740),
        p = i(p, v, d, g, m[c + 1], 4, 2763975236),
        g = i(g, p, v, d, m[c + 4], 11, 1272893353),
        d = i(d, g, p, v, m[c + 7], 16, 4139469664),
        v = i(v, d, g, p, m[c + 10], 23, 3200236656),
        p = i(p, v, d, g, m[c + 13], 4, 681279174),
        g = i(g, p, v, d, m[c + 0], 11, 3936430074),
        d = i(d, g, p, v, m[c + 3], 16, 3572445317),
        v = i(v, d, g, p, m[c + 6], 23, 76029189),
        p = i(p, v, d, g, m[c + 9], 4, 3654602809),
        g = i(g, p, v, d, m[c + 12], 11, 3873151461),
        d = i(d, g, p, v, m[c + 15], 16, 530742520),
        p = u(p, v = i(v, d, g, p, m[c + 2], 23, 3299628645), d, g, m[c + 0], 6, 4096336452),
        g = u(g, p, v, d, m[c + 7], 10, 1126891415),
        d = u(d, g, p, v, m[c + 14], 15, 2878612391),
        v = u(v, d, g, p, m[c + 5], 21, 4237533241),
        p = u(p, v, d, g, m[c + 12], 6, 1700485571),
        g = u(g, p, v, d, m[c + 3], 10, 2399980690),
        d = u(d, g, p, v, m[c + 10], 15, 4293915773),
        v = u(v, d, g, p, m[c + 1], 21, 2240044497),
        p = u(p, v, d, g, m[c + 8], 6, 1873313359),
        g = u(g, p, v, d, m[c + 15], 10, 4264355552),
        d = u(d, g, p, v, m[c + 6], 15, 2734768916),
        v = u(v, d, g, p, m[c + 13], 21, 1309151649),
        p = u(p, v, d, g, m[c + 4], 6, 4149444226),
        g = u(g, p, v, d, m[c + 11], 10, 3174756917),
        d = u(d, g, p, v, m[c + 2], 15, 718787259),
        v = u(v, d, g, p, m[c + 9], 21, 3951481745),
        p = r(p, l),
        v = r(v, s),
        d = r(d, a),
        g = r(g, h);
    return (f(p) + f(v) + f(d) + f(g)).toLowerCase()
};
gReceiver_("fuuuuuuuuuck");
"""

def sign_query(query):
    return js2py.eval_js(JS_FUNC.replace("fuuuuuuuuuck", query))

def save_estates():
    print('Persisting {} estates, {} sold estates.'.format(len(EstateSet), len(SoldEstateSet)))
    with open(SALE_FILE_NAME, 'wb') as handle:
        pickle.dump(EstateSet, handle, protocol=pickle.HIGHEST_PROTOCOL)
    with open(SOLD_FILE_NAME, 'wb') as handle:
        pickle.dump(SoldEstateSet, handle, protocol=pickle.HIGHEST_PROTOCOL)


LON_START = -123.4
LON_END = -121.9
LAT_START = 48.9
LAT_END = 49.43
STEPS = 3
LON_STEP = (LON_END - LON_START) / STEPS
LAT_STEP = (LAT_END - LAT_START) / STEPS

class Estate(object):
    def __init__(self, lineitem):
        self.history_price = []
        self.history_sold_price = []
        self.assessment_price = []
        self.list_price = None
        self.sell_price = None
        self.sell_time = None
        self.estate_code = None
        self.area = None
        self.city = None
        self.rew = None
        self.do_update(lineitem)

    def __str__(self):
        return "{} | {} | {} | {} | {} | {} | {} | {}".format(self.id, self.city, self.area, self.address, self.list_price, self.history_price, self.assessment_price, self.history_sold_price)

    def html(self):
        content = '<td><a href="{}">{}</a></td>\n'.format(self.get_rew_link(), self.id)
        content += "<td>{}</td>\n".format(self.address)
        content += "<td>{}</td>\n".format(self.area)
        content += "<td>{}</td>\n".format(self.list_price)
        content += "<td>{}</td>\n".format(', '.join([str(s) for s in self.history_price]))
        if self.assessment_price is None:
            assessment = "NOT FOUND"
        else:
            assessment = ', '.join([str(s) for s in self.assessment_price])
        content += "<td>{}</td>\n".format(assessment)
        content += "<td>{}</td>\n".format('<br>\n'.join([str(s) for s in self.history_sold_price]))
        return content

    def get_rew_link(self):
        if self.rew is None:
            try:
                r = requests.get("https://www.rew.ca/properties/search/build", params={"listing_search[query]": self.id})
                self.rew = "https://www.rew.ca{}".format(r.json()['path'])
            except:
                self.rew = ""
        return self.rew

    def do_update(self, lineitem):
        self.id = lineitem[0]
        self.address = lineitem[5].lstrip("#").strip()
        self.area = lineitem[6]
        list_price = float(lineitem[7]) * 1000
        if self.list_price is None:
            self.list_price = list_price
        else:
            if self.list_price != list_price:
                self.history_price.append(self.list_price)
                self.list_price = list_price
            else:
                pass
        if len(self.history_price):
            pass
        else:
            # init history price
            if len(lineitem[25]):
                history_price = float(lineitem[25]) * 1000
                if history_price > 0:
                    self.history_price.append(history_price)
        self.age = int(lineitem[11])
        self.bedroom = int(lineitem[12])
        self.bathroom = int(lineitem[13])
        self.size = int(lineitem[14])
        self.tax = float(lineitem[27])
        try:
            self.sell_price = float(lineitem[32]) * 1000
        except:
            self.sell_price = None
        self.sell_time = lineitem[33]
        self.city = lineitem[36]
        self.fee = float(lineitem[82])
        self.last_update = datetime.now()

    def parse_info_from_bc_assessment(self, code):
        self.estate_code = code
        url = "https://www.bcassessment.ca/Property/Info/{}".format(self.estate_code)
        r = requests.get(url, timeout=BC_ASSESSMENT_TIMEOUT)
        if r.status_code == 200:
            soup = BeautifulSoup(r.text, 'html.parser')
            def to_price(result):
                if result is None:
                    raise RuntimeError("BeautifulSoup failed to find node for {}".format(url))
                return float(result.text.lstrip("$").replace(",", ""))
            def to_sales(result):
                s = result.text.split("$")
                return s[0].strip("\n"), float(s[-1].replace(",", ""))
            self.assessment_price = []
            self.assessment_price.append(to_price(soup.find(id="lblTotalAssessedValue")))
            try:
                self.assessment_price.append(to_price(soup.find(id="lblPreviousAssessedValue")))
                self.history_sold_price = [to_sales(i) for i in soup.find_all("tr", {"class": "salesrow"})]
            except:
                pass
        else:
            print("BC assessment returns {} for {}".format(r.status_code, url))

    def __update_bc_assessment_impl(self):
        try:
            r = requests.get("https://www.bcassessment.ca/Property/Search/GetByAddress", params={"addr": self.address}, timeout=BC_ASSESSMENT_TIMEOUT)
            if r.status_code == 200:
                estate_id = r.json()[0]["value"]
                if str(estate_id) == "0":
                    print("Invalid BC assessment ID={} for {}".format(estate_id, self.address))
                else:
                    self.parse_info_from_bc_assessment(estate_id)
            else:
                print("BC assessment returns {} for {}".format(r.status_code, self.address))
        except Exception as e:
            print("Failed to fetch assessment for {} from BC: {}".format(self.address, str(e)))

    def __update_bc_assessment_rew(self):
        try:
            r = requests.get("https://www.rew.ca/properties/search/build", params={"listing_search[query]": self.id})
            if r.status_code != 200:
                raise RuntimeError("REW returns {} status code".format(r.status_code))
            listing_id = r.json()['path'].split('/')[2]
            headers = {
                'user-agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/92.0.4515.107 Safari/537.36',
                'content-type': 'application/json'
            }
            r = requests.post("https://www.rew.ca/graphql/rew-portal", headers=headers, data='{"operationName":"assessments","variables":{"listingId":%s},"query":"query assessments($listingId: ID\u0021) {\\n  assessmentHistory(listingId: $listingId) {\\n    value\\n    valuePercentChange\\n    landValue\\n    buildingValue\\n    valuationDate\\n    __typename\\n  }\\n}\\n"}' % (listing_id))
            if r.status_code == 200:
                history = r.json()["data"]["assessmentHistory"]
                self.assessment_price = [x["value"] for x in history]
                return
            else:
                print("REW assessment returns {}".format(r.status_code))
        except Exception as e:
            # if can not find that price, thus just set to None
            print("Failed to fetch assessment for {} from REW: {}".format(self.address, str(e)))

    def has_assessment_price(self):
        if self.assessment_price is not None:
            while len(self.assessment_price) and self.assessment_price[0] < 1000:
                self.assessment_price.pop(0)
        return self.assessment_price is not None and len(self.assessment_price)

    def is_exclude(self):
        return (self.has_assessment_price() and (self.list_price - self.assessment_price[0]) / self.assessment_price[0] < -0.5) or self.city in EXCLUDE_CITY

    def update_bc_assessment(self):
        if self.has_assessment_price():
            return
        if self.assessment_price is None:
            return
        self.__update_bc_assessment_impl()
        if not self.has_assessment_price():
            self.__update_bc_assessment_rew()
        if not self.has_assessment_price():
            self.assessment_price = None
        else:
            print(self)

    def is_sold(self):
        return self.sell_price is not None

    def update(self):
        if (datetime.now() - self.last_update).days <= ESTATE_SLA:
            return
        if self.is_sold():
            return
        print("Updating estate [{}]".format(self.address))
        query = r"SELECT * FROM *** WHERE mlsNumber = '{}' LIMIT 200".format(self.id)
        r = requests.post("https://bcrealestatemap.ca/svcFetchDB.php", data = {
            "sql": query,
            "sold": 1,
            "s": sign_query(query)
        })
        if r.status_code == 200:
            js = r.json()
            if "rows" in js:
                lineitem = js["rows"]
                if len(lineitem):
                    self.do_update(lineitem[0])
                    print("Moving [{}] from list to sold.".format(self.address))
                    EstateSet.pop(self.id)
                    SoldEstateSet[self.id] = self

class Worker(object):
    def __init__(self):
        self.on_sale_query_list = []
        self.sold_query_list = []
        self.debug = bool(os.getenv('debug', 0))
        self.new_estates = []
        self.previous_good_price_estates = {}
        self.new_sold_estate_count = 0
        self.current_day = self.get_date()

    def init_query(self):
        self.sold_query_list = []
        for i in range(0, STEPS):
            for j in range(0, STEPS):
                query = r"SELECT * FROM *** WHERE (latitude BETWEEN {} AND {}) AND (longitude BETWEEN {} AND {}) AND (latitude <> 0 AND longitude <> 0) AND ((propertyClassCode = 0) OR (propertyClassCode = 1 AND type <> 'Apartment')) AND reciprocityOK = 0 AND (ABS(soldPrice) >= 600) AND (ABS(soldPrice) <= 1250) AND (entryDate BETWEEN '{}' AND '{}') ORDER BY entryDate DESC LIMIT 500".format(
                    LAT_START + i * LAT_STEP,
                    LAT_START + (i + 1) * LAT_STEP,
                    LON_START + j * LON_STEP,
                    LON_START + (j + 1) * LON_STEP,
                    self.get_date_str(90),
                    self.get_date_str()
                )
                self.sold_query_list.append((query, sign_query(query)))
        if len(self.on_sale_query_list):
            return
        for i in range(0, STEPS):
            for j in range(0, STEPS):
                query = r"SELECT * FROM *** WHERE (latitude BETWEEN {} AND {}) AND (longitude BETWEEN {} AND {}) AND (latitude <> 0 AND longitude <> 0) AND ((propertyClassCode = 0) OR (propertyClassCode = 1 AND type <> 'Apartment')) AND parkingInfo LIKE '%Garage%' AND reciprocityOK = 0 AND (listingPrice >= 600) AND (listingPrice <= 1100) LIMIT 500".format(
                    LAT_START + i * LAT_STEP,
                    LAT_START + (i + 1) * LAT_STEP,
                    LON_START + j * LON_STEP,
                    LON_START + (j + 1) * LON_STEP
                )
                self.on_sale_query_list.append((query, sign_query(query)))
    
    def get_date(self):
        return datetime.now(pytz.timezone('US/Pacific')).date()
    
    def get_date_str(self, minus_days=0):
        return (datetime.now() - timedelta(days=minus_days)).strftime("%Y-%m-%d")

    def do_work(self):
        self.scan_estates()
        self.update_database()
        self.do_statistics()
        save_estates()

    def scan_estates(self):
        self.init_query()
        self.new_estates = []
        self.new_sold_estate_count = 0
        estates = self.query_estates(self.sold_query_list, 1)
        for l in estates:
            e = Estate(l)
            if e.id not in SoldEstateSet:
                self.new_sold_estate_count += 1
                SoldEstateSet[e.id] = e
            else:
                e = SoldEstateSet[e.id]
                e.do_update(l)
        print("Found {} new sold estates".format(self.new_sold_estate_count))
        estates = self.query_estates(self.on_sale_query_list, None)
        for l in estates:
            e = Estate(l)
            if e.id not in EstateSet and e.id not in SoldEstateSet:
                self.new_estates.append(e)
                EstateSet[e.id] = e
                print("Found new estate {}".format(e.address))
            else:
                e = EstateSet[e.id]
                e.do_update(l)
        print("Found {} new estates".format(len(self.new_estates)))

    def update_database(self):
        sold_count = 0
        for estate in EstateSet.values():
            estate.update()
            estate.update_bc_assessment()
        for estate in SoldEstateSet.values():
            estate.update()
            estate.update_bc_assessment()
            if estate.id in EstateSet:
                EstateSet.pop(estate.id)
                print("Moving [{}] from list to sold.".format(estate.address))
                sold_count += 1
        print("Removed {} sold estates from selling list.".format(sold_count))

    def do_statistics(self):
        good_price_estates = []
        estates_no_assessment = 0
        for estate in EstateSet.values():
            if not estate.has_assessment_price():
                estates_no_assessment += 1
            else:
                try:
                    rate = (estate.list_price - estate.assessment_price[0]) / estate.list_price
                    if rate < GOOD_PRICE_UPPER_THRESHOLD and rate > GOOD_PRICE_LOWER_THRESHOLD and estate.city not in EXCLUDE_CITY:
                        good_price_estates.append((rate, estate))
                except:
                    pass
        good_price_estates.sort(key=lambda x: x[0])
        good_price_estates_grouped = {}
        for r, e in good_price_estates:
            if e.city in good_price_estates_grouped:
                good_price_estates_grouped[e.city].append((r, e))
            else:
                good_price_estates_grouped[e.city] = [(r, e)]
        content = ""
        self.new_estates = [e for e in self.new_estates if e.city not in EXCLUDE_CITY]
        if len(self.new_estates):
            content += u"<h2>新上线房产</h2><br>\n"
            content += '<table border="1" style="width:100%">\n'
            content += u"""
                <tr>
                <th>ID</th>
                <th>地址</th>
                <th>区域</th>
                <th>卖价</th>
                <th>历史卖价</th>
                <th>评估价</th>
                <th>历史交易价</th>
                </tr>
                """
            content += "\n".join(["<tr>{}</tr>".format(e.html()) for e in self.new_estates])
            content += "</table><br><br>\n"
        content += u"<h2>低溢价房产</h2>\n"
        for city in good_price_estates_grouped.keys():
            content += "<br><br><h3>{}</h3>\n<br><br>".format(city)
            content += '<table border="1">\n'
            content += u"""
            <tr>
            <th>加价比例</th>
            <th>ID</th>
            <th>地址</th>
            <th>区域</th>
            <th>卖价</th>
            <th>历史卖价</th>
            <th>评估价</th>
            <th>历史交易价</th>
            </tr>
            """
            for r, e in good_price_estates_grouped[city]:
                if e.id in self.previous_good_price_estates:
                    tr = "<tr>"
                else:
                    tr = '<tr style="background-color:#FFF933">'
                content += "{}\n".format(tr)
                content += "<td>{:.2f}%</td>\n".format(r * 100)
                content += e.html()
                content += "</tr>\n"
            content += "</table>\n"
        content += u"\n\n<p>总计 {} ({:.1f}%) 处房产未能找到BC省评估价格.</p>\n".format(estates_no_assessment, float(estates_no_assessment) / len(EstateSet) * 100)
        if self.debug:
            print(content)
        self.send_mail(content)
        self.previous_good_price_estates = set([e.id for _, e in good_price_estates])
        
    def send_mail(self, content):
        sender = os.environ['smtp_email']
        password = os.environ['smtp_password']
        msg = MIMEMultipart('alternative')
        msg['Subject'] = u"温哥华地产数据报告"
        msg['To'] = EMAIL_LIST[0]
        msg['From'] = sender
        fnames = self.plot()
        images = [base64.b64encode(open(f, 'rb').read()).decode("utf-8") for f in fnames]
        for f in fnames:
            os.remove(f)
        images_html = "\n<br>\n".join(['<img src="data:image/png;base64,{}" />'.format(i) for i in images])
        text = MIMEText('{}\n{}'.format(images_html, content), 'html')
        msg.attach(text)
        smtp = smtplib.SMTP_SSL("smtp.163.com", 465)
        print("SMTP connect successfully")
        smtp.login(sender, password)
        print("login successfully")
        smtp.sendmail(sender, EMAIL_LIST, msg.as_string())
        print("sendmail successfully")
        smtp.close()

    def loop(self):
        counter = 0
        while True:
            time.sleep(1)
            if (self.get_date() != self.current_day) or self.debug:
                self.current_day = self.get_date()
                try:
                    print("Time's up, do work!")
                    self.do_work()
                except Exception as e:
                    print("worker exception: {}".format(str(e)))
                if self.debug:
                    sys.exit(0)
            else:
                if counter % 600 == 0:
                    print("hearbeating...")
            counter += 1

    def query_estates(self, query_list, sold):
        lineitems = []
        for q, s in query_list:
            r = requests.post("https://bcrealestatemap.ca/svcFetchDB.php", data = {
                "sql": q,
                "sold": sold,
                "s": s
            })
            if r.status_code == 200:
                js = r.json()
                if "rows" in js:
                    lineitems += js["rows"]
        print("Current estates on list with sold={}: {}".format(sold, len(lineitems)))
        return lineitems

    def load_estate_info(self):
        pass
    
    def filter_sold_estates_by_date(self, start, end):
        def to_datetime(s):
            try:
                return parser.parse(s)
            except:
                return datetime.now()
        return [e for e in SoldEstateSet.values() if e.has_assessment_price() and not e.is_exclude() and to_datetime(e.sell_time) >= start and to_datetime(e.sell_time) <= end]

    def plot_for_list_estates(self):
        bins = 40
        plot_range = (-3e5, 3e5)
        def formatter(x, pos):
            return "{:.1f}w".format(x / 10000.)
        estates = [e for e in EstateSet.values() if e.has_assessment_price() and not e.is_exclude()]
        fig, ax = plt.subplots(nrows=1, ncols=1, tight_layout=True, figsize=(5, 5))
        ax.xaxis.set_major_formatter(FuncFormatter(formatter))
        list_prices = np.array([e.list_price for e in estates])
        assessment_prices = np.array([e.assessment_price[0] for e in estates])
        ax.hist(list_prices - assessment_prices, bins=bins, range=plot_range)
        ax.set_title(u"ask price - assessment price")
        fname = "list.png"
        fig.savefig(fname)
        return fname

    def plot_for_time_range(self, start, end):
        bins = 40
        plot_range = (-3e5, 3e5)
        def formatter(x, pos):
            return "{:.1f}w".format(x / 10000.)
        fig, axs = plt.subplots(nrows=1, ncols=3, tight_layout=True, figsize=(12, 4))
        fig.suptitle('{} to {}'.format(start.strftime("%Y-%m-%d"), end.strftime("%Y-%m-%d")))
        for ax in axs:
            ax.xaxis.set_major_formatter(FuncFormatter(formatter))
        estates = self.filter_sold_estates_by_date(start, end)
        sell_prices = np.array([e.sell_price for e in estates])
        list_prices = np.array([e.list_price for e in estates])
        assessment_prices = np.array([e.assessment_price[0] for e in estates])
        axs[0].hist(sell_prices, bins=bins)
        axs[0].set_title(u"sell price")
        axs[1].hist(sell_prices - list_prices, bins=bins, range=plot_range)
        axs[1].set_title(u"sell price - ask price")
        axs[2].hist(sell_prices - assessment_prices, bins=bins, range=plot_range)
        axs[2].set_title(u"sell price - assessment price")
        fname = '{} {}.png'.format(start.strftime("%Y-%m-%d"), end.strftime("%Y-%m-%d"))
        fig.savefig(fname)
        return fname

    def plot(self):
        return [
            self.plot_for_list_estates(),
            self.plot_for_time_range(datetime.now() - timedelta(days=14), datetime.now()),
            self.plot_for_time_range(datetime.now() - timedelta(days=30), datetime.now()),
            self.plot_for_time_range(datetime.now() - timedelta(days=60), datetime.now() - timedelta(days=30)),
            self.plot_for_time_range(datetime.now() - timedelta(days=90), datetime.now() - timedelta(days=60))
        ]

def signal_handler(sig, frame):
    save_estates()
    os._exit(1)


def main():
    w = Worker()
    w.loop()


if __name__ == '__main__':
    signal.signal(signal.SIGINT, signal_handler)
    if os.path.exists(SALE_FILE_NAME):
        with open(SALE_FILE_NAME, 'rb') as handle:
            EstateSet = pickle.load(handle)
            print("Successfully loaded {} sale estates.".format(len(EstateSet)))
    if os.path.exists(SOLD_FILE_NAME):
        with open(SOLD_FILE_NAME, 'rb') as handle:
            SoldEstateSet = pickle.load(handle)
            print("Successfully loaded {} sold estates.".format(len(SoldEstateSet)))
    # for e in list(EstateSet.values()) + list(SoldEstateSet.values()):
    #     if getattr(e, "rew", None) is None:
    #         setattr(e, "rew", None)
    main()