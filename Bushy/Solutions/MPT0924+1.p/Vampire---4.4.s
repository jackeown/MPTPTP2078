%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t84_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  399 (1155 expanded)
%              Number of leaves         :  105 ( 474 expanded)
%              Depth                    :   10
%              Number of atoms          :  937 (3042 expanded)
%              Number of equality atoms :   13 (  55 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f79,f102,f111,f118,f125,f134,f141,f148,f155,f183,f201,f203,f214,f221,f232,f247,f254,f277,f292,f307,f366,f382,f389,f424,f440,f447,f492,f505,f512,f519,f535,f542,f567,f569,f588,f595,f611,f618,f625,f641,f648,f655,f671,f678,f744,f751,f758,f774,f781,f788,f804,f825,f832,f848,f855,f1073,f1089,f1096,f1103,f1119,f1126,f1133,f1149,f1156,f1163,f1179,f1198,f2008,f2024,f2031,f2038,f2054,f2061,f2068,f2084,f2091,f2111,f2127,f2134,f2141,f2157,f2164,f2268,f2271,f2272,f2274,f2276,f2277,f2279,f2280,f2282,f2283,f2294,f2296,f2306,f2307,f2350,f2366,f2373,f2964,f2965,f2975,f2977])).

fof(f2977,plain,
    ( spl9_7
    | ~ spl9_160 ),
    inference(avatar_contradiction_clause,[],[f2976])).

fof(f2976,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f2967,f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK0,sK4)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_7
  <=> ~ r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2967,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl9_160 ),
    inference(resolution,[],[f2264,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t106_zfmisc_1)).

fof(f2264,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_160 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2263,plain,
    ( spl9_160
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f2975,plain,
    ( spl9_13
    | ~ spl9_160 ),
    inference(avatar_contradiction_clause,[],[f2974])).

fof(f2974,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f2966,f121])).

fof(f121,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_13
  <=> ~ r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f2966,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl9_160 ),
    inference(resolution,[],[f2264,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2965,plain,
    ( spl9_160
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f2962,f94,f2263])).

fof(f94,plain,
    ( spl9_4
  <=> r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2962,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_4 ),
    inference(resolution,[],[f1057,f95])).

fof(f95,plain,
    ( r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1057,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X4,X5)) ) ),
    inference(superposition,[],[f159,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(forward_demodulation,[],[f86,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',d4_mcart_1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(superposition,[],[f55,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',d3_mcart_1)).

fof(f159,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X4,X5,X6),k4_zfmisc_1(X0,X1,X2,X3))
      | r2_hidden(X4,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t54_mcart_1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t73_mcart_1)).

fof(f2964,plain,
    ( ~ spl9_4
    | spl9_161 ),
    inference(avatar_contradiction_clause,[],[f2963])).

fof(f2963,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_161 ),
    inference(subsumption_resolution,[],[f2962,f2267])).

fof(f2267,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_161 ),
    inference(avatar_component_clause,[],[f2266])).

fof(f2266,plain,
    ( spl9_161
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).

fof(f2373,plain,
    ( ~ spl9_167
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f2357,f2348,f2371])).

fof(f2371,plain,
    ( spl9_167
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))),k4_tarski(sK2,k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_167])])).

fof(f2348,plain,
    ( spl9_162
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f2357,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))),k4_tarski(sK2,k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3))))
    | ~ spl9_162 ),
    inference(resolution,[],[f2349,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',antisymmetry_r2_hidden)).

fof(f2349,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))))
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f2348])).

fof(f2366,plain,
    ( ~ spl9_165
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f2358,f2348,f2364])).

fof(f2364,plain,
    ( spl9_165
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).

fof(f2358,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))))
    | ~ spl9_162 ),
    inference(resolution,[],[f2349,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t7_boole)).

fof(f2350,plain,
    ( spl9_162
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f2300,f364,f139,f2348])).

fof(f139,plain,
    ( spl9_16
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f364,plain,
    ( spl9_40
  <=> r2_hidden(k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3)),k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f2300,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))))
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(resolution,[],[f365,f205])).

fof(f205,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,X2)
        | r2_hidden(k4_tarski(sK2,X1),k2_zfmisc_1(sK6,X2)) )
    | ~ spl9_16 ),
    inference(resolution,[],[f140,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f365,plain,
    ( r2_hidden(k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3)),k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f364])).

fof(f2307,plain,
    ( spl9_124
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f2142,f2139,f1161])).

fof(f1161,plain,
    ( spl9_124
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f2139,plain,
    ( spl9_154
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f2142,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))
    | ~ spl9_154 ),
    inference(resolution,[],[f2140,f59])).

fof(f2140,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))))
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f2139])).

fof(f2306,plain,
    ( spl9_112
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2069,f2066,f1101])).

fof(f1101,plain,
    ( spl9_112
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f2066,plain,
    ( spl9_142
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f2069,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))
    | ~ spl9_142 ),
    inference(resolution,[],[f2067,f59])).

fof(f2067,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))))
    | ~ spl9_142 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f2296,plain,
    ( spl9_119
    | ~ spl9_148 ),
    inference(avatar_contradiction_clause,[],[f2295])).

fof(f2295,plain,
    ( $false
    | ~ spl9_119
    | ~ spl9_148 ),
    inference(subsumption_resolution,[],[f1129,f2112])).

fof(f2112,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))
    | ~ spl9_148 ),
    inference(resolution,[],[f2110,f59])).

fof(f2110,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))))
    | ~ spl9_148 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f2109,plain,
    ( spl9_148
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).

fof(f1129,plain,
    ( ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))
    | ~ spl9_119 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1128,plain,
    ( spl9_119
  <=> ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f2294,plain,
    ( spl9_94
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f1134,f1131,f786])).

fof(f786,plain,
    ( spl9_94
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f1131,plain,
    ( spl9_118
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f1134,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))
    | ~ spl9_118 ),
    inference(resolution,[],[f1132,f59])).

fof(f1132,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))
    | ~ spl9_118 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f2283,plain,
    ( spl9_4
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f367,f364,f94])).

fof(f367,plain,
    ( r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl9_40 ),
    inference(resolution,[],[f365,f59])).

fof(f2282,plain,
    ( spl9_101
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f2281])).

fof(f2281,plain,
    ( $false
    | ~ spl9_101
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f828,f1164])).

fof(f1164,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))
    | ~ spl9_124 ),
    inference(resolution,[],[f1162,f59])).

fof(f1162,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f828,plain,
    ( ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))
    | ~ spl9_101 ),
    inference(avatar_component_clause,[],[f827])).

fof(f827,plain,
    ( spl9_101
  <=> ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f2280,plain,
    ( spl9_78
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f833,f830,f653])).

fof(f653,plain,
    ( spl9_78
  <=> r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f830,plain,
    ( spl9_100
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f833,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK6,sK5))
    | ~ spl9_100 ),
    inference(resolution,[],[f831,f59])).

fof(f831,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f830])).

fof(f2279,plain,
    ( spl9_89
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f2278])).

fof(f2278,plain,
    ( $false
    | ~ spl9_89
    | ~ spl9_112 ),
    inference(subsumption_resolution,[],[f754,f1104])).

fof(f1104,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))
    | ~ spl9_112 ),
    inference(resolution,[],[f1102,f59])).

fof(f1102,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))
    | ~ spl9_112 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f754,plain,
    ( ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))
    | ~ spl9_89 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl9_89
  <=> ~ r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f2277,plain,
    ( spl9_22
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f759,f756,f181])).

fof(f181,plain,
    ( spl9_22
  <=> r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f756,plain,
    ( spl9_88
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f759,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK4,sK4))
    | ~ spl9_88 ),
    inference(resolution,[],[f757,f59])).

fof(f757,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f756])).

fof(f2276,plain,
    ( spl9_7
    | ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f2275])).

fof(f2275,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f98,f596])).

fof(f596,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl9_22 ),
    inference(resolution,[],[f182,f59])).

fof(f182,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK4,sK4))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f2274,plain,
    ( spl9_73
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f2273])).

fof(f2273,plain,
    ( $false
    | ~ spl9_73
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f621,f789])).

fof(f789,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4))
    | ~ spl9_94 ),
    inference(resolution,[],[f787,f59])).

fof(f787,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f786])).

fof(f621,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4))
    | ~ spl9_73 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl9_73
  <=> ~ r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f2272,plain,
    ( spl9_6
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f626,f623,f100])).

fof(f100,plain,
    ( spl9_6
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f623,plain,
    ( spl9_72
  <=> r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f626,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl9_72 ),
    inference(resolution,[],[f624,f59])).

fof(f624,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f623])).

fof(f2271,plain,
    ( ~ spl9_6
    | ~ spl9_12
    | spl9_161 ),
    inference(avatar_contradiction_clause,[],[f2270])).

fof(f2270,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_161 ),
    inference(subsumption_resolution,[],[f2269,f124])).

fof(f124,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_12
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2269,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ spl9_6
    | ~ spl9_161 ),
    inference(resolution,[],[f2267,f573])).

fof(f573,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(sK0,X5),k2_zfmisc_1(sK4,X6))
        | ~ r2_hidden(X5,X6) )
    | ~ spl9_6 ),
    inference(resolution,[],[f101,f60])).

fof(f101,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f2268,plain,
    ( ~ spl9_161
    | spl9_5
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f2259,f153,f139,f91,f2266])).

fof(f91,plain,
    ( spl9_5
  <=> ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f153,plain,
    ( spl9_20
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f2259,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_5
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f2251,f140])).

fof(f2251,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_5
    | ~ spl9_20 ),
    inference(resolution,[],[f1315,f92])).

fof(f92,plain,
    ( ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1315,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( r2_hidden(k4_mcart_1(X3,X4,X5,sK3),k4_zfmisc_1(X0,X1,X2,sK7))
        | ~ r2_hidden(X5,X2)
        | ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X0,X1)) )
    | ~ spl9_20 ),
    inference(superposition,[],[f706,f56])).

fof(f706,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,sK3),k3_zfmisc_1(X3,X4,sK7))
        | ~ r2_hidden(X2,X4)
        | ~ r2_hidden(k4_tarski(X0,X1),X3) )
    | ~ spl9_20 ),
    inference(superposition,[],[f493,f87])).

fof(f493,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k3_mcart_1(X0,X1,sK3),k3_zfmisc_1(X2,X3,sK7))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl9_20 ),
    inference(resolution,[],[f154,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X2,X5)
      | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f154,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2164,plain,
    ( ~ spl9_159
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f2148,f2139,f2162])).

fof(f2162,plain,
    ( spl9_159
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).

fof(f2148,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1)))))
    | ~ spl9_154 ),
    inference(resolution,[],[f2140,f50])).

fof(f2157,plain,
    ( ~ spl9_157
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f2149,f2139,f2155])).

fof(f2155,plain,
    ( spl9_157
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_157])])).

fof(f2149,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))))
    | ~ spl9_154 ),
    inference(resolution,[],[f2140,f54])).

fof(f2141,plain,
    ( spl9_154
    | ~ spl9_16
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f1167,f1161,f139,f2139])).

fof(f1167,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))))
    | ~ spl9_16
    | ~ spl9_124 ),
    inference(resolution,[],[f1162,f205])).

fof(f2134,plain,
    ( ~ spl9_153
    | ~ spl9_148 ),
    inference(avatar_split_clause,[],[f2118,f2109,f2132])).

fof(f2132,plain,
    ( spl9_153
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f2118,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0)))))
    | ~ spl9_148 ),
    inference(resolution,[],[f2110,f50])).

fof(f2127,plain,
    ( ~ spl9_151
    | ~ spl9_148 ),
    inference(avatar_split_clause,[],[f2119,f2109,f2125])).

fof(f2125,plain,
    ( spl9_151
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_151])])).

fof(f2119,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))))
    | ~ spl9_148 ),
    inference(resolution,[],[f2110,f54])).

fof(f2111,plain,
    ( spl9_148
    | ~ spl9_16
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f1137,f1131,f139,f2109])).

fof(f1137,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))))
    | ~ spl9_16
    | ~ spl9_118 ),
    inference(resolution,[],[f1132,f205])).

fof(f2091,plain,
    ( ~ spl9_147
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2075,f2066,f2089])).

fof(f2089,plain,
    ( spl9_147
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f2075,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0)))))
    | ~ spl9_142 ),
    inference(resolution,[],[f2067,f50])).

fof(f2084,plain,
    ( ~ spl9_145
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2076,f2066,f2082])).

fof(f2082,plain,
    ( spl9_145
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f2076,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))))
    | ~ spl9_142 ),
    inference(resolution,[],[f2067,f54])).

fof(f2068,plain,
    ( spl9_142
    | ~ spl9_16
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f1107,f1101,f139,f2066])).

fof(f1107,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))))
    | ~ spl9_16
    | ~ spl9_112 ),
    inference(resolution,[],[f1102,f205])).

fof(f2061,plain,
    ( ~ spl9_141
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f2045,f2036,f2059])).

fof(f2059,plain,
    ( spl9_141
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).

fof(f2036,plain,
    ( spl9_136
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f2045,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3)))))
    | ~ spl9_136 ),
    inference(resolution,[],[f2037,f50])).

fof(f2037,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))))
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f2036])).

fof(f2054,plain,
    ( ~ spl9_139
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f2046,f2036,f2052])).

fof(f2052,plain,
    ( spl9_139
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f2046,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))))
    | ~ spl9_136 ),
    inference(resolution,[],[f2037,f54])).

fof(f2038,plain,
    ( spl9_136
    | ~ spl9_16
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f1077,f1071,f139,f2036])).

fof(f1071,plain,
    ( spl9_106
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f1077,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))))
    | ~ spl9_16
    | ~ spl9_106 ),
    inference(resolution,[],[f1072,f205])).

fof(f1072,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f2031,plain,
    ( ~ spl9_135
    | ~ spl9_130 ),
    inference(avatar_split_clause,[],[f2015,f2006,f2029])).

fof(f2029,plain,
    ( spl9_135
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f2006,plain,
    ( spl9_130
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f2015,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))))
    | ~ spl9_130 ),
    inference(resolution,[],[f2007,f50])).

fof(f2007,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))))
    | ~ spl9_130 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2024,plain,
    ( ~ spl9_133
    | ~ spl9_130 ),
    inference(avatar_split_clause,[],[f2016,f2006,f2022])).

fof(f2022,plain,
    ( spl9_133
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f2016,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))))
    | ~ spl9_130 ),
    inference(resolution,[],[f2007,f54])).

fof(f2008,plain,
    ( spl9_130
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f428,f422,f139,f2006])).

fof(f422,plain,
    ( spl9_46
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f428,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))))
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(resolution,[],[f423,f205])).

fof(f423,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1198,plain,
    ( ~ spl9_129
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f1170,f1161,f1196])).

fof(f1196,plain,
    ( spl9_129
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f1170,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))))
    | ~ spl9_124 ),
    inference(resolution,[],[f1162,f50])).

fof(f1179,plain,
    ( ~ spl9_127
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f1171,f1161,f1177])).

fof(f1177,plain,
    ( spl9_127
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f1171,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))
    | ~ spl9_124 ),
    inference(resolution,[],[f1162,f54])).

fof(f1163,plain,
    ( spl9_124
    | ~ spl9_16
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f836,f830,f139,f1161])).

fof(f836,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK1))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))))
    | ~ spl9_16
    | ~ spl9_100 ),
    inference(resolution,[],[f831,f205])).

fof(f1156,plain,
    ( ~ spl9_123
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f1140,f1131,f1154])).

fof(f1154,plain,
    ( spl9_123
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f1140,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))))
    | ~ spl9_118 ),
    inference(resolution,[],[f1132,f50])).

fof(f1149,plain,
    ( ~ spl9_121
    | ~ spl9_118 ),
    inference(avatar_split_clause,[],[f1141,f1131,f1147])).

fof(f1147,plain,
    ( spl9_121
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f1141,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))
    | ~ spl9_118 ),
    inference(resolution,[],[f1132,f54])).

fof(f1133,plain,
    ( spl9_118
    | ~ spl9_16
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f792,f786,f139,f1131])).

fof(f792,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))))
    | ~ spl9_16
    | ~ spl9_94 ),
    inference(resolution,[],[f787,f205])).

fof(f1126,plain,
    ( ~ spl9_117
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f1110,f1101,f1124])).

fof(f1124,plain,
    ( spl9_117
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f1110,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))))
    | ~ spl9_112 ),
    inference(resolution,[],[f1102,f50])).

fof(f1119,plain,
    ( ~ spl9_115
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f1111,f1101,f1117])).

fof(f1117,plain,
    ( spl9_115
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f1111,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))
    | ~ spl9_112 ),
    inference(resolution,[],[f1102,f54])).

fof(f1103,plain,
    ( spl9_112
    | ~ spl9_16
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f762,f756,f139,f1101])).

fof(f762,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK0,sK0))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))))
    | ~ spl9_16
    | ~ spl9_88 ),
    inference(resolution,[],[f757,f205])).

fof(f1096,plain,
    ( ~ spl9_111
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f1080,f1071,f1094])).

fof(f1094,plain,
    ( spl9_111
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f1080,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3))))
    | ~ spl9_106 ),
    inference(resolution,[],[f1072,f50])).

fof(f1089,plain,
    ( ~ spl9_109
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f1081,f1071,f1087])).

fof(f1087,plain,
    ( spl9_109
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f1081,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))))
    | ~ spl9_106 ),
    inference(resolution,[],[f1072,f54])).

fof(f1073,plain,
    ( spl9_106
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f732,f565,f139,f1071])).

fof(f565,plain,
    ( spl9_62
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK3)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f732,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK3))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(resolution,[],[f566,f205])).

fof(f566,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK3)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f565])).

fof(f855,plain,
    ( ~ spl9_105
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f839,f830,f853])).

fof(f853,plain,
    ( spl9_105
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)),k4_tarski(sK2,k4_tarski(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f839,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)),k4_tarski(sK2,k4_tarski(sK2,sK1)))
    | ~ spl9_100 ),
    inference(resolution,[],[f831,f50])).

fof(f848,plain,
    ( ~ spl9_103
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f840,f830,f846])).

fof(f846,plain,
    ( spl9_103
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f840,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))
    | ~ spl9_100 ),
    inference(resolution,[],[f831,f54])).

fof(f832,plain,
    ( spl9_100
    | ~ spl9_16
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f659,f653,f139,f830])).

fof(f659,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK5)))
    | ~ spl9_16
    | ~ spl9_78 ),
    inference(resolution,[],[f654,f205])).

fof(f654,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK6,sK5))
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f653])).

fof(f825,plain,
    ( ~ spl9_99
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f795,f786,f823])).

fof(f823,plain,
    ( spl9_99
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)),k4_tarski(sK2,k4_tarski(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f795,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)),k4_tarski(sK2,k4_tarski(sK2,sK0)))
    | ~ spl9_94 ),
    inference(resolution,[],[f787,f50])).

fof(f804,plain,
    ( ~ spl9_97
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f796,f786,f802])).

fof(f802,plain,
    ( spl9_97
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f796,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))
    | ~ spl9_94 ),
    inference(resolution,[],[f787,f54])).

fof(f788,plain,
    ( spl9_94
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f629,f623,f139,f786])).

fof(f629,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK4)))
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(resolution,[],[f624,f205])).

fof(f781,plain,
    ( ~ spl9_93
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f765,f756,f779])).

fof(f779,plain,
    ( spl9_93
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)),k4_tarski(sK2,k4_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f765,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)),k4_tarski(sK2,k4_tarski(sK0,sK0)))
    | ~ spl9_88 ),
    inference(resolution,[],[f757,f50])).

fof(f774,plain,
    ( ~ spl9_91
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f766,f756,f772])).

fof(f772,plain,
    ( spl9_91
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f766,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))
    | ~ spl9_88 ),
    inference(resolution,[],[f757,f54])).

fof(f758,plain,
    ( spl9_88
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f599,f181,f139,f756])).

fof(f599,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK4,sK4)))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(resolution,[],[f182,f205])).

fof(f751,plain,
    ( ~ spl9_87
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f735,f565,f749])).

fof(f749,plain,
    ( spl9_87
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)),k4_tarski(sK2,k4_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f735,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)),k4_tarski(sK2,k4_tarski(sK2,sK3)))
    | ~ spl9_62 ),
    inference(resolution,[],[f566,f50])).

fof(f744,plain,
    ( ~ spl9_85
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f736,f565,f742])).

fof(f742,plain,
    ( spl9_85
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f736,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))
    | ~ spl9_62 ),
    inference(resolution,[],[f566,f54])).

fof(f678,plain,
    ( ~ spl9_83
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f662,f653,f676])).

fof(f676,plain,
    ( spl9_83
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,sK5),k4_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f662,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,sK5),k4_tarski(sK2,sK1))
    | ~ spl9_78 ),
    inference(resolution,[],[f654,f50])).

fof(f671,plain,
    ( ~ spl9_81
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f663,f653,f669])).

fof(f669,plain,
    ( spl9_81
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f663,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,sK5))
    | ~ spl9_78 ),
    inference(resolution,[],[f654,f54])).

fof(f655,plain,
    ( spl9_78
    | ~ spl9_12
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f577,f139,f123,f653])).

fof(f577,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK6,sK5))
    | ~ spl9_12
    | ~ spl9_16 ),
    inference(resolution,[],[f124,f205])).

fof(f648,plain,
    ( ~ spl9_77
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f632,f623,f646])).

fof(f646,plain,
    ( spl9_77
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,sK4),k4_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f632,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,sK4),k4_tarski(sK2,sK0))
    | ~ spl9_72 ),
    inference(resolution,[],[f624,f50])).

fof(f641,plain,
    ( ~ spl9_75
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f633,f623,f639])).

fof(f639,plain,
    ( spl9_75
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f633,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,sK4))
    | ~ spl9_72 ),
    inference(resolution,[],[f624,f54])).

fof(f625,plain,
    ( spl9_72
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f571,f139,f100,f623])).

fof(f571,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK6,sK4))
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(resolution,[],[f101,f205])).

fof(f618,plain,
    ( ~ spl9_71
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f602,f181,f616])).

fof(f616,plain,
    ( spl9_71
  <=> ~ r2_hidden(k2_zfmisc_1(sK4,sK4),k4_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f602,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK4,sK4),k4_tarski(sK0,sK0))
    | ~ spl9_22 ),
    inference(resolution,[],[f182,f50])).

fof(f611,plain,
    ( ~ spl9_69
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f603,f181,f609])).

fof(f609,plain,
    ( spl9_69
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f603,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,sK4))
    | ~ spl9_22 ),
    inference(resolution,[],[f182,f54])).

fof(f595,plain,
    ( ~ spl9_67
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f580,f123,f593])).

fof(f593,plain,
    ( spl9_67
  <=> ~ r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f580,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl9_12 ),
    inference(resolution,[],[f124,f50])).

fof(f588,plain,
    ( ~ spl9_65
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f581,f123,f586])).

fof(f586,plain,
    ( spl9_65
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f581,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl9_12 ),
    inference(resolution,[],[f124,f54])).

fof(f569,plain,
    ( spl9_5
    | ~ spl9_40 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f92,f367])).

fof(f567,plain,
    ( spl9_62
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f523,f517,f139,f565])).

fof(f517,plain,
    ( spl9_56
  <=> r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f523,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK3)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK7)))
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(resolution,[],[f518,f205])).

fof(f518,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK6,sK7))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f517])).

fof(f542,plain,
    ( ~ spl9_61
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f526,f517,f540])).

fof(f540,plain,
    ( spl9_61
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,sK7),k4_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f526,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,sK7),k4_tarski(sK2,sK3))
    | ~ spl9_56 ),
    inference(resolution,[],[f518,f50])).

fof(f535,plain,
    ( ~ spl9_59
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f527,f517,f533])).

fof(f533,plain,
    ( spl9_59
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f527,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7))
    | ~ spl9_56 ),
    inference(resolution,[],[f518,f54])).

fof(f519,plain,
    ( spl9_56
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f494,f153,f139,f517])).

fof(f494,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK6,sK7))
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(resolution,[],[f154,f205])).

fof(f512,plain,
    ( ~ spl9_55
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f497,f153,f510])).

fof(f510,plain,
    ( spl9_55
  <=> ~ r2_hidden(sK7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f497,plain,
    ( ~ r2_hidden(sK7,sK3)
    | ~ spl9_20 ),
    inference(resolution,[],[f154,f50])).

fof(f505,plain,
    ( ~ spl9_53
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f498,f153,f503])).

fof(f503,plain,
    ( spl9_53
  <=> ~ v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f498,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl9_20 ),
    inference(resolution,[],[f154,f54])).

fof(f492,plain,
    ( spl9_20
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f491,f94,f153])).

fof(f491,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl9_4 ),
    inference(resolution,[],[f187,f95])).

fof(f187,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | r2_hidden(X3,X7) ) ),
    inference(superposition,[],[f161,f87])).

fof(f161,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X4,X5,X6),k4_zfmisc_1(X0,X1,X2,X3))
      | r2_hidden(X6,X3) ) ),
    inference(superposition,[],[f63,f56])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | r2_hidden(X2,X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f447,plain,
    ( ~ spl9_51
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f431,f422,f445])).

fof(f445,plain,
    ( spl9_51
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f431,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))))
    | ~ spl9_46 ),
    inference(resolution,[],[f423,f50])).

fof(f440,plain,
    ( ~ spl9_49
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f432,f422,f438])).

fof(f438,plain,
    ( spl9_49
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f432,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))))
    | ~ spl9_46 ),
    inference(resolution,[],[f423,f54])).

fof(f424,plain,
    ( spl9_46
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f280,f275,f139,f422])).

fof(f275,plain,
    ( spl9_34
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f280,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(resolution,[],[f276,f205])).

fof(f276,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f275])).

fof(f389,plain,
    ( ~ spl9_45
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f373,f364,f387])).

fof(f387,plain,
    ( spl9_45
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)),k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f373,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)),k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_40 ),
    inference(resolution,[],[f365,f50])).

fof(f382,plain,
    ( ~ spl9_43
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f374,f364,f380])).

fof(f380,plain,
    ( spl9_43
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f374,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)))
    | ~ spl9_40 ),
    inference(resolution,[],[f365,f54])).

fof(f366,plain,
    ( spl9_40
    | ~ spl9_4
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f222,f139,f94,f364])).

fof(f222,plain,
    ( r2_hidden(k4_tarski(sK2,k4_mcart_1(sK0,sK1,sK2,sK3)),k2_zfmisc_1(sK6,k4_zfmisc_1(sK4,sK5,sK6,sK7)))
    | ~ spl9_4
    | ~ spl9_16 ),
    inference(resolution,[],[f205,f95])).

fof(f307,plain,
    ( ~ spl9_39
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f283,f275,f305])).

fof(f305,plain,
    ( spl9_39
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)),k4_tarski(sK2,k4_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f283,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)),k4_tarski(sK2,k4_tarski(sK2,sK2)))
    | ~ spl9_34 ),
    inference(resolution,[],[f276,f50])).

fof(f292,plain,
    ( ~ spl9_37
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f284,f275,f290])).

fof(f290,plain,
    ( spl9_37
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f284,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))
    | ~ spl9_34 ),
    inference(resolution,[],[f276,f54])).

fof(f277,plain,
    ( spl9_34
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f235,f230,f139,f275])).

fof(f230,plain,
    ( spl9_28
  <=> r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f235,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK6,k2_zfmisc_1(sK6,sK6)))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(resolution,[],[f231,f205])).

fof(f231,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK6,sK6))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f254,plain,
    ( ~ spl9_33
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f238,f230,f252])).

fof(f252,plain,
    ( spl9_33
  <=> ~ r2_hidden(k2_zfmisc_1(sK6,sK6),k4_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f238,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK6,sK6),k4_tarski(sK2,sK2))
    | ~ spl9_28 ),
    inference(resolution,[],[f231,f50])).

fof(f247,plain,
    ( ~ spl9_31
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f239,f230,f245])).

fof(f245,plain,
    ( spl9_31
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK6,sK6))
    | ~ spl9_28 ),
    inference(resolution,[],[f231,f54])).

fof(f232,plain,
    ( spl9_28
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f224,f139,f230])).

fof(f224,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK6,sK6))
    | ~ spl9_16 ),
    inference(resolution,[],[f205,f140])).

fof(f221,plain,
    ( ~ spl9_27
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f206,f139,f219])).

fof(f219,plain,
    ( spl9_27
  <=> ~ r2_hidden(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f206,plain,
    ( ~ r2_hidden(sK6,sK2)
    | ~ spl9_16 ),
    inference(resolution,[],[f140,f50])).

fof(f214,plain,
    ( ~ spl9_25
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f207,f139,f212])).

fof(f212,plain,
    ( spl9_25
  <=> ~ v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f207,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ spl9_16 ),
    inference(resolution,[],[f140,f54])).

fof(f203,plain,
    ( spl9_16
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f202,f94,f139])).

fof(f202,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl9_4 ),
    inference(resolution,[],[f186,f95])).

fof(f186,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | r2_hidden(X2,X6) ) ),
    inference(superposition,[],[f160,f87])).

fof(f160,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X4,X5,X6),k4_zfmisc_1(X0,X1,X2,X3))
      | r2_hidden(X5,X2) ) ),
    inference(superposition,[],[f62,f56])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | r2_hidden(X1,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f201,plain,
    ( ~ spl9_5
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f46,f150,f136,f120,f97,f91])).

fof(f136,plain,
    ( spl9_17
  <=> ~ r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f150,plain,
    ( spl9_21
  <=> ~ r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f46,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(sK0,sK4)
      | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
    & ( ( r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5)
        & r2_hidden(sK0,sK4) )
      | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK0,sK4)
        | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & ( ( r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5)
          & r2_hidden(sK0,sK4) )
        | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t84_mcart_1)).

fof(f183,plain,
    ( spl9_22
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f175,f100,f181])).

fof(f175,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK4,sK4))
    | ~ spl9_6 ),
    inference(resolution,[],[f170,f101])).

fof(f170,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | r2_hidden(k4_tarski(sK0,X3),k2_zfmisc_1(sK4,X4)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f60,f101])).

fof(f155,plain,
    ( spl9_4
    | spl9_20 ),
    inference(avatar_split_clause,[],[f45,f153,f94])).

fof(f45,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f148,plain,
    ( ~ spl9_19
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f126,f94,f146])).

fof(f146,plain,
    ( spl9_19
  <=> ~ r2_hidden(k4_zfmisc_1(sK4,sK5,sK6,sK7),k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f126,plain,
    ( ~ r2_hidden(k4_zfmisc_1(sK4,sK5,sK6,sK7),k4_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f50])).

fof(f141,plain,
    ( spl9_4
    | spl9_16 ),
    inference(avatar_split_clause,[],[f44,f139,f94])).

fof(f44,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,
    ( ~ spl9_15
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f127,f94,f132])).

fof(f132,plain,
    ( spl9_15
  <=> ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f127,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f54])).

fof(f125,plain,
    ( spl9_4
    | spl9_12 ),
    inference(avatar_split_clause,[],[f43,f123,f94])).

fof(f43,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,
    ( ~ spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f103,f100,f116])).

fof(f116,plain,
    ( spl9_11
  <=> ~ r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f103,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f101,f50])).

fof(f111,plain,
    ( ~ spl9_9
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f104,f100,f109])).

fof(f109,plain,
    ( spl9_9
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl9_6 ),
    inference(resolution,[],[f101,f54])).

fof(f102,plain,
    ( spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f42,f100,f94])).

fof(f42,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,
    ( spl9_2
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f72,f69,f77])).

fof(f77,plain,
    ( spl9_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f69,plain,
    ( spl9_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f72,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_0 ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t6_boole)).

fof(f71,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f47,f69])).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
