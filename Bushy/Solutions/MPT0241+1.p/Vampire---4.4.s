%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t36_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  578 (1628 expanded)
%              Number of leaves         :  126 ( 639 expanded)
%              Depth                    :   12
%              Number of atoms          : 1574 (4201 expanded)
%              Number of equality atoms :  235 (1112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f111,f116,f130,f132,f137,f151,f156,f170,f172,f176,f179,f197,f206,f210,f213,f232,f239,f261,f266,f268,f282,f290,f294,f308,f313,f330,f354,f379,f396,f403,f418,f456,f463,f478,f485,f544,f731,f785,f786,f787,f1077,f1084,f1135,f1164,f1168,f1340,f1352,f1368,f1389,f1396,f1400,f1411,f1655,f1671,f1719,f1742,f1762,f1788,f1795,f1824,f1829,f1854,f1859,f1861,f1879,f1881,f1889,f1891,f1909,f1969,f1973,f2089,f2111,f2118,f2125,f2132,f2147,f2156,f2238,f2239,f2246,f2258,f2702,f2742,f2798,f2821,f2831,f2847,f2852,f2869,f2874,f2887,f2912,f2920,f2924,f2946,f2952,f2976,f2982,f3004,f3012,f3038,f3044,f3058,f3095,f3104,f3157,f3259,f3263,f3380,f3384,f3389,f3392])).

fof(f3392,plain,
    ( spl11_13
    | ~ spl11_108 ),
    inference(avatar_contradiction_clause,[],[f3391])).

fof(f3391,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_108 ),
    inference(subsumption_resolution,[],[f3390,f56])).

fof(f56,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',d2_tarski)).

fof(f3390,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_13
    | ~ spl11_108 ),
    inference(forward_demodulation,[],[f144,f1902])).

fof(f1902,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_108 ),
    inference(avatar_component_clause,[],[f1901])).

fof(f1901,plain,
    ( spl11_108
  <=> k4_tarski(sK0,sK1) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f144,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_13
  <=> ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f3389,plain,
    ( spl11_19
    | spl11_31
    | spl11_33 ),
    inference(avatar_contradiction_clause,[],[f3388])).

fof(f3388,plain,
    ( $false
    | ~ spl11_19
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3387,f56])).

fof(f3387,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_19
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f169,f264])).

fof(f264,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f263,f260])).

fof(f260,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl11_33
  <=> ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f263,plain,
    ( r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_31 ),
    inference(resolution,[],[f254,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',t2_tarski)).

fof(f254,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl11_31
  <=> ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f169,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl11_19
  <=> ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f3384,plain,(
    spl11_181 ),
    inference(avatar_contradiction_clause,[],[f3383])).

fof(f3383,plain,
    ( $false
    | ~ spl11_181 ),
    inference(subsumption_resolution,[],[f3382,f56])).

fof(f3382,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl11_181 ),
    inference(subsumption_resolution,[],[f3381,f60])).

fof(f60,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',d1_tarski)).

fof(f3381,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl11_181 ),
    inference(resolution,[],[f3379,f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',d2_zfmisc_1)).

fof(f3379,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_181 ),
    inference(avatar_component_clause,[],[f3378])).

fof(f3378,plain,
    ( spl11_181
  <=> ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_181])])).

fof(f3380,plain,
    ( ~ spl11_181
    | spl11_7
    | ~ spl11_174 ),
    inference(avatar_split_clause,[],[f3265,f3149,f109,f3378])).

fof(f109,plain,
    ( spl11_7
  <=> ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f3149,plain,
    ( spl11_174
  <=> k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_174])])).

fof(f3265,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_7
    | ~ spl11_174 ),
    inference(backward_demodulation,[],[f3150,f110])).

fof(f110,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f3150,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_174 ),
    inference(avatar_component_clause,[],[f3149])).

fof(f3263,plain,(
    spl11_179 ),
    inference(avatar_contradiction_clause,[],[f3262])).

fof(f3262,plain,
    ( $false
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f3261,f54])).

fof(f54,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3261,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f3260,f60])).

fof(f3260,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl11_179 ),
    inference(resolution,[],[f3258,f49])).

fof(f3258,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_179 ),
    inference(avatar_component_clause,[],[f3257])).

fof(f3257,plain,
    ( spl11_179
  <=> ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_179])])).

fof(f3259,plain,
    ( ~ spl11_179
    | spl11_7
    | ~ spl11_176 ),
    inference(avatar_split_clause,[],[f3159,f3155,f109,f3257])).

fof(f3155,plain,
    ( spl11_176
  <=> k4_tarski(sK1,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_176])])).

fof(f3159,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_7
    | ~ spl11_176 ),
    inference(backward_demodulation,[],[f3156,f110])).

fof(f3156,plain,
    ( k4_tarski(sK1,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_176 ),
    inference(avatar_component_clause,[],[f3155])).

fof(f3157,plain,
    ( spl11_174
    | spl11_176
    | spl11_1
    | spl11_7 ),
    inference(avatar_split_clause,[],[f2814,f109,f65,f3155,f3149])).

fof(f65,plain,
    ( spl11_1
  <=> k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f2814,plain,
    ( k4_tarski(sK1,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_1
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2812,f66])).

fof(f66,plain,
    ( k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f2812,plain,
    ( k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | k4_tarski(sK1,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_7 ),
    inference(resolution,[],[f110,f90])).

fof(f90,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK10(k2_tarski(X2,X3),X4),X4)
      | k2_tarski(X2,X3) = X4
      | sK10(k2_tarski(X2,X3),X4) = X3
      | sK10(k2_tarski(X2,X3),X4) = X2 ) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3104,plain,
    ( spl11_166
    | spl11_137
    | spl11_169 ),
    inference(avatar_split_clause,[],[f3045,f3036,f2697,f3027])).

fof(f3027,plain,
    ( spl11_166
  <=> r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_166])])).

fof(f2697,plain,
    ( spl11_137
  <=> sK0 != sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_137])])).

fof(f3036,plain,
    ( spl11_169
  <=> ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_169])])).

fof(f3045,plain,
    ( r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0)
    | ~ spl11_137
    | ~ spl11_169 ),
    inference(subsumption_resolution,[],[f3041,f2698])).

fof(f2698,plain,
    ( sK0 != sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_137 ),
    inference(avatar_component_clause,[],[f2697])).

fof(f3041,plain,
    ( r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0)
    | sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_169 ),
    inference(resolution,[],[f3037,f42])).

fof(f3037,plain,
    ( ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_169 ),
    inference(avatar_component_clause,[],[f3036])).

fof(f3095,plain,
    ( spl11_137
    | spl11_171
    | spl11_173 ),
    inference(avatar_contradiction_clause,[],[f3094])).

fof(f3094,plain,
    ( $false
    | ~ spl11_137
    | ~ spl11_171
    | ~ spl11_173 ),
    inference(subsumption_resolution,[],[f3093,f2698])).

fof(f3093,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_171
    | ~ spl11_173 ),
    inference(subsumption_resolution,[],[f3092,f3057])).

fof(f3057,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK0)
    | ~ spl11_173 ),
    inference(avatar_component_clause,[],[f3056])).

fof(f3056,plain,
    ( spl11_173
  <=> ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_173])])).

fof(f3092,plain,
    ( r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK0)
    | sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_171 ),
    inference(resolution,[],[f3051,f42])).

fof(f3051,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_171 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl11_171
  <=> ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_171])])).

fof(f3058,plain,
    ( ~ spl11_171
    | ~ spl11_173
    | spl11_137 ),
    inference(avatar_split_clause,[],[f3025,f2697,f3056,f3050])).

fof(f3025,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK0)
    | ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK0),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_137 ),
    inference(extensionality_resolution,[],[f43,f2698])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | ~ r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3044,plain,
    ( spl11_137
    | spl11_167
    | spl11_169 ),
    inference(avatar_contradiction_clause,[],[f3043])).

fof(f3043,plain,
    ( $false
    | ~ spl11_137
    | ~ spl11_167
    | ~ spl11_169 ),
    inference(subsumption_resolution,[],[f3042,f2698])).

fof(f3042,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_167
    | ~ spl11_169 ),
    inference(subsumption_resolution,[],[f3041,f3031])).

fof(f3031,plain,
    ( ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0)
    | ~ spl11_167 ),
    inference(avatar_component_clause,[],[f3030])).

fof(f3030,plain,
    ( spl11_167
  <=> ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_167])])).

fof(f3038,plain,
    ( ~ spl11_167
    | ~ spl11_169
    | spl11_137 ),
    inference(avatar_split_clause,[],[f3024,f2697,f3036,f3030])).

fof(f3024,plain,
    ( ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ r2_hidden(sK10(sK0,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK0)
    | ~ spl11_137 ),
    inference(extensionality_resolution,[],[f43,f2698])).

fof(f3012,plain,
    ( spl11_135
    | spl11_163
    | spl11_165 ),
    inference(avatar_contradiction_clause,[],[f3011])).

fof(f3011,plain,
    ( $false
    | ~ spl11_135
    | ~ spl11_163
    | ~ spl11_165 ),
    inference(subsumption_resolution,[],[f3010,f2692])).

fof(f2692,plain,
    ( sK1 != sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_135 ),
    inference(avatar_component_clause,[],[f2691])).

fof(f2691,plain,
    ( spl11_135
  <=> sK1 != sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_135])])).

fof(f3010,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_163
    | ~ spl11_165 ),
    inference(subsumption_resolution,[],[f3009,f3003])).

fof(f3003,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK1)
    | ~ spl11_165 ),
    inference(avatar_component_clause,[],[f3002])).

fof(f3002,plain,
    ( spl11_165
  <=> ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_165])])).

fof(f3009,plain,
    ( r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK1)
    | sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_163 ),
    inference(resolution,[],[f2997,f42])).

fof(f2997,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_163 ),
    inference(avatar_component_clause,[],[f2996])).

fof(f2996,plain,
    ( spl11_163
  <=> ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_163])])).

fof(f3004,plain,
    ( ~ spl11_163
    | ~ spl11_165
    | spl11_135 ),
    inference(avatar_split_clause,[],[f2963,f2691,f3002,f2996])).

fof(f2963,plain,
    ( ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK1)
    | ~ r2_hidden(sK10(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK1),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_135 ),
    inference(extensionality_resolution,[],[f43,f2692])).

fof(f2982,plain,
    ( spl11_135
    | spl11_159
    | spl11_161 ),
    inference(avatar_contradiction_clause,[],[f2981])).

fof(f2981,plain,
    ( $false
    | ~ spl11_135
    | ~ spl11_159
    | ~ spl11_161 ),
    inference(subsumption_resolution,[],[f2980,f2692])).

fof(f2980,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_159
    | ~ spl11_161 ),
    inference(subsumption_resolution,[],[f2979,f2969])).

fof(f2969,plain,
    ( ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK1)
    | ~ spl11_159 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f2968,plain,
    ( spl11_159
  <=> ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_159])])).

fof(f2979,plain,
    ( r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK1)
    | sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_161 ),
    inference(resolution,[],[f2975,f42])).

fof(f2975,plain,
    ( ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_161 ),
    inference(avatar_component_clause,[],[f2974])).

fof(f2974,plain,
    ( spl11_161
  <=> ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_161])])).

fof(f2976,plain,
    ( ~ spl11_159
    | ~ spl11_161
    | spl11_135 ),
    inference(avatar_split_clause,[],[f2962,f2691,f2974,f2968])).

fof(f2962,plain,
    ( ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ r2_hidden(sK10(sK1,sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK1)
    | ~ spl11_135 ),
    inference(extensionality_resolution,[],[f43,f2692])).

fof(f2952,plain,
    ( spl11_39
    | spl11_155
    | spl11_157 ),
    inference(avatar_contradiction_clause,[],[f2951])).

fof(f2951,plain,
    ( $false
    | ~ spl11_39
    | ~ spl11_155
    | ~ spl11_157 ),
    inference(subsumption_resolution,[],[f2950,f286])).

fof(f286,plain,
    ( sK2 != sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl11_39
  <=> sK2 != sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f2950,plain,
    ( sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_155
    | ~ spl11_157 ),
    inference(subsumption_resolution,[],[f2949,f2945])).

fof(f2945,plain,
    ( ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK2)
    | ~ spl11_157 ),
    inference(avatar_component_clause,[],[f2944])).

fof(f2944,plain,
    ( spl11_157
  <=> ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_157])])).

fof(f2949,plain,
    ( r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK2)
    | sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_155 ),
    inference(resolution,[],[f2939,f42])).

fof(f2939,plain,
    ( ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_155 ),
    inference(avatar_component_clause,[],[f2938])).

fof(f2938,plain,
    ( spl11_155
  <=> ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_155])])).

fof(f2946,plain,
    ( ~ spl11_155
    | ~ spl11_157
    | spl11_39 ),
    inference(avatar_split_clause,[],[f2899,f285,f2944,f2938])).

fof(f2899,plain,
    ( ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK2)
    | ~ r2_hidden(sK10(sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_39 ),
    inference(extensionality_resolution,[],[f43,f286])).

fof(f2924,plain,
    ( spl11_39
    | spl11_149
    | spl11_151 ),
    inference(avatar_contradiction_clause,[],[f2923])).

fof(f2923,plain,
    ( $false
    | ~ spl11_39
    | ~ spl11_149
    | ~ spl11_151 ),
    inference(subsumption_resolution,[],[f2922,f286])).

fof(f2922,plain,
    ( sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_149
    | ~ spl11_151 ),
    inference(subsumption_resolution,[],[f2921,f2905])).

fof(f2905,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK2)
    | ~ spl11_149 ),
    inference(avatar_component_clause,[],[f2904])).

fof(f2904,plain,
    ( spl11_149
  <=> ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_149])])).

fof(f2921,plain,
    ( r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK2)
    | sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_151 ),
    inference(resolution,[],[f2911,f42])).

fof(f2911,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ spl11_151 ),
    inference(avatar_component_clause,[],[f2910])).

fof(f2910,plain,
    ( spl11_151
  <=> ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_151])])).

fof(f2920,plain,
    ( spl11_152
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f2897,f1901,f1717,f476,f2918])).

fof(f2918,plain,
    ( spl11_152
  <=> sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_152])])).

fof(f476,plain,
    ( spl11_58
  <=> k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f1717,plain,
    ( spl11_90
  <=> sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f2897,plain,
    ( sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1))
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(resolution,[],[f2297,f60])).

fof(f2297,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK0,k1_tarski(X4))
        | sK4(k1_tarski(X4),k1_tarski(sK1),k4_tarski(sK0,sK1)) = X4 )
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(resolution,[],[f1982,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | sK4(k1_tarski(X1),X2,X0) = X1 ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1982,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(X1,k1_tarski(sK1)))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1981,f1921])).

fof(f1921,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(X1,k1_tarski(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1)))))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl11_58
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1902,f1698])).

fof(f1698,plain,
    ( ! [X1] :
        ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(X1,k1_tarski(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl11_58 ),
    inference(resolution,[],[f490,f60])).

fof(f490,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),X10)
        | r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(X9,X10))
        | ~ r2_hidden(sK0,X9) )
    | ~ spl11_58 ),
    inference(superposition,[],[f49,f477])).

fof(f477,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f476])).

fof(f1981,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1))
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(forward_demodulation,[],[f1718,f1902])).

fof(f1718,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_90 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f2912,plain,
    ( ~ spl11_149
    | ~ spl11_151
    | spl11_39 ),
    inference(avatar_split_clause,[],[f2898,f285,f2910,f2904])).

fof(f2898,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))))
    | ~ r2_hidden(sK10(sK2,sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))),sK2)
    | ~ spl11_39 ),
    inference(extensionality_resolution,[],[f43,f286])).

fof(f2887,plain,
    ( spl11_142
    | spl11_49
    | spl11_141 ),
    inference(avatar_split_clause,[],[f2853,f2839,f391,f2842])).

fof(f2842,plain,
    ( spl11_142
  <=> r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).

fof(f391,plain,
    ( spl11_49
  <=> k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) != sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f2839,plain,
    ( spl11_141
  <=> ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_141])])).

fof(f2853,plain,
    ( r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_49
    | ~ spl11_141 ),
    inference(subsumption_resolution,[],[f2849,f392])).

fof(f392,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) != sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f391])).

fof(f2849,plain,
    ( r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_141 ),
    inference(resolution,[],[f2840,f42])).

fof(f2840,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2))
    | ~ spl11_141 ),
    inference(avatar_component_clause,[],[f2839])).

fof(f2874,plain,
    ( spl11_49
    | spl11_145
    | spl11_147 ),
    inference(avatar_contradiction_clause,[],[f2873])).

fof(f2873,plain,
    ( $false
    | ~ spl11_49
    | ~ spl11_145
    | ~ spl11_147 ),
    inference(subsumption_resolution,[],[f2872,f392])).

fof(f2872,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_145
    | ~ spl11_147 ),
    inference(subsumption_resolution,[],[f2871,f2862])).

fof(f2862,plain,
    ( ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_145 ),
    inference(avatar_component_clause,[],[f2861])).

fof(f2861,plain,
    ( spl11_145
  <=> ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_145])])).

fof(f2871,plain,
    ( r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_147 ),
    inference(resolution,[],[f2868,f42])).

fof(f2868,plain,
    ( ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2))
    | ~ spl11_147 ),
    inference(avatar_component_clause,[],[f2867])).

fof(f2867,plain,
    ( spl11_147
  <=> ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_147])])).

fof(f2869,plain,
    ( ~ spl11_145
    | ~ spl11_147
    | spl11_49 ),
    inference(avatar_split_clause,[],[f2833,f391,f2867,f2861])).

fof(f2833,plain,
    ( ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2))
    | ~ r2_hidden(sK10(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2)),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_49 ),
    inference(extensionality_resolution,[],[f43,f392])).

fof(f2852,plain,
    ( spl11_49
    | spl11_141
    | spl11_143 ),
    inference(avatar_contradiction_clause,[],[f2851])).

fof(f2851,plain,
    ( $false
    | ~ spl11_49
    | ~ spl11_141
    | ~ spl11_143 ),
    inference(subsumption_resolution,[],[f2850,f392])).

fof(f2850,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_141
    | ~ spl11_143 ),
    inference(subsumption_resolution,[],[f2849,f2846])).

fof(f2846,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_143 ),
    inference(avatar_component_clause,[],[f2845])).

fof(f2845,plain,
    ( spl11_143
  <=> ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_143])])).

fof(f2847,plain,
    ( ~ spl11_141
    | ~ spl11_143
    | spl11_49 ),
    inference(avatar_split_clause,[],[f2832,f391,f2845,f2839])).

fof(f2832,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ r2_hidden(sK10(k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2))
    | ~ spl11_49 ),
    inference(extensionality_resolution,[],[f43,f392])).

fof(f2831,plain,
    ( ~ spl11_5
    | ~ spl11_7
    | spl11_1 ),
    inference(avatar_split_clause,[],[f1398,f65,f109,f103])).

fof(f103,plain,
    ( spl11_5
  <=> ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1398,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_1 ),
    inference(extensionality_resolution,[],[f43,f66])).

fof(f2821,plain,
    ( spl11_138
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f2665,f1901,f1717,f476,f2819])).

fof(f2819,plain,
    ( spl11_138
  <=> sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_138])])).

fof(f2665,plain,
    ( sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1))
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(resolution,[],[f2295,f60])).

fof(f2295,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | sK1 = sK5(X2,k1_tarski(sK1),k4_tarski(sK0,sK1)) )
    | ~ spl11_58
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(resolution,[],[f1982,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | sK5(X1,k1_tarski(X2),X0) = X2 ) ),
    inference(resolution,[],[f51,f58])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2798,plain,
    ( spl11_5
    | ~ spl11_48
    | ~ spl11_134 ),
    inference(avatar_contradiction_clause,[],[f2797])).

fof(f2797,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_48
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f2768,f54])).

fof(f2768,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_5
    | ~ spl11_48
    | ~ spl11_134 ),
    inference(backward_demodulation,[],[f2758,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f2758,plain,
    ( k4_tarski(sK1,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_48
    | ~ spl11_134 ),
    inference(backward_demodulation,[],[f2695,f395])).

fof(f395,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl11_48
  <=> k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f2695,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_134 ),
    inference(avatar_component_clause,[],[f2694])).

fof(f2694,plain,
    ( spl11_134
  <=> sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_134])])).

fof(f2742,plain,
    ( spl11_5
    | ~ spl11_48
    | ~ spl11_136 ),
    inference(avatar_contradiction_clause,[],[f2741])).

fof(f2741,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_48
    | ~ spl11_136 ),
    inference(subsumption_resolution,[],[f2713,f56])).

fof(f2713,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_5
    | ~ spl11_48
    | ~ spl11_136 ),
    inference(backward_demodulation,[],[f2703,f104])).

fof(f2703,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_48
    | ~ spl11_136 ),
    inference(backward_demodulation,[],[f2701,f395])).

fof(f2701,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_136 ),
    inference(avatar_component_clause,[],[f2700])).

fof(f2700,plain,
    ( spl11_136
  <=> sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_136])])).

fof(f2702,plain,
    ( spl11_134
    | spl11_136
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f608,f106,f2700,f2694])).

fof(f106,plain,
    ( spl11_6
  <=> r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f608,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | sK1 = sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_6 ),
    inference(resolution,[],[f84,f107])).

fof(f107,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f84,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X11,k2_zfmisc_1(k2_tarski(X9,X8),X10))
      | sK4(k2_tarski(X9,X8),X10,X11) = X9
      | sK4(k2_tarski(X9,X8),X10,X11) = X8 ) ),
    inference(resolution,[],[f57,f52])).

fof(f2258,plain,
    ( spl11_132
    | ~ spl11_90
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f1981,f1901,f1717,f2256])).

fof(f2256,plain,
    ( spl11_132
  <=> sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_132])])).

fof(f2246,plain,
    ( spl11_130
    | ~ spl11_2
    | spl11_31
    | spl11_33 ),
    inference(avatar_split_clause,[],[f2081,f259,f253,f68,f2244])).

fof(f2244,plain,
    ( spl11_130
  <=> k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_130])])).

fof(f68,plain,
    ( spl11_2
  <=> k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2081,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_2
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f69,f264])).

fof(f69,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f2239,plain,
    ( ~ spl11_123
    | ~ spl11_121
    | ~ spl11_2
    | spl11_23
    | spl11_31
    | spl11_33 ),
    inference(avatar_split_clause,[],[f2136,f259,f253,f192,f68,f2123,f2127])).

fof(f2127,plain,
    ( spl11_123
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_123])])).

fof(f2123,plain,
    ( spl11_121
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).

fof(f192,plain,
    ( spl11_23
  <=> k4_tarski(sK0,sK2) != sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f2136,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK2))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_2
    | ~ spl11_23
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f2135,f2081])).

fof(f2135,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),k4_tarski(sK0,sK2))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_2
    | ~ spl11_23
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f2134,f69])).

fof(f2134,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | ~ spl11_2
    | ~ spl11_23
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f2133,f2081])).

fof(f2133,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | ~ spl11_2
    | ~ spl11_23 ),
    inference(forward_demodulation,[],[f1467,f69])).

fof(f1467,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | ~ spl11_23 ),
    inference(extensionality_resolution,[],[f43,f193])).

fof(f193,plain,
    ( k4_tarski(sK0,sK2) != sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f2238,plain,
    ( spl11_128
    | ~ spl11_68
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f1919,f1901,f1075,f2236])).

fof(f2236,plain,
    ( spl11_128
  <=> sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_128])])).

fof(f1075,plain,
    ( spl11_68
  <=> sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f1919,plain,
    ( sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1))
    | ~ spl11_68
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1902,f1076])).

fof(f1076,plain,
    ( sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f2156,plain,
    ( spl11_126
    | spl11_31
    | spl11_33
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f2020,f303,f259,f253,f2154])).

fof(f2154,plain,
    ( spl11_126
  <=> r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_126])])).

fof(f303,plain,
    ( spl11_42
  <=> r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f2020,plain,
    ( r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | ~ spl11_31
    | ~ spl11_33
    | ~ spl11_42 ),
    inference(backward_demodulation,[],[f264,f304])).

fof(f304,plain,
    ( r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f303])).

fof(f2147,plain,
    ( ~ spl11_125
    | spl11_31
    | spl11_33
    | spl11_41 ),
    inference(avatar_split_clause,[],[f2019,f300,f259,f253,f2145])).

fof(f2145,plain,
    ( spl11_125
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f300,plain,
    ( spl11_41
  <=> ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f2019,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK1))
    | ~ spl11_31
    | ~ spl11_33
    | ~ spl11_41 ),
    inference(backward_demodulation,[],[f264,f301])).

fof(f301,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f300])).

fof(f2132,plain,
    ( spl11_122
    | spl11_31
    | spl11_33
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f2018,f277,f259,f253,f2130])).

fof(f2130,plain,
    ( spl11_122
  <=> r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_122])])).

fof(f277,plain,
    ( spl11_36
  <=> r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f2018,plain,
    ( r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_31
    | ~ spl11_33
    | ~ spl11_36 ),
    inference(backward_demodulation,[],[f264,f278])).

fof(f278,plain,
    ( r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f2125,plain,
    ( ~ spl11_121
    | spl11_31
    | spl11_33
    | spl11_35 ),
    inference(avatar_split_clause,[],[f2017,f274,f259,f253,f2123])).

fof(f274,plain,
    ( spl11_35
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f2017,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK2))
    | ~ spl11_31
    | ~ spl11_33
    | ~ spl11_35 ),
    inference(backward_demodulation,[],[f264,f275])).

fof(f275,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f274])).

fof(f2118,plain,
    ( ~ spl11_119
    | ~ spl11_108
    | spl11_111 ),
    inference(avatar_split_clause,[],[f1955,f1904,f1901,f2116])).

fof(f2116,plain,
    ( spl11_119
  <=> k4_tarski(sK0,sK1) != k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_119])])).

fof(f1904,plain,
    ( spl11_111
  <=> k4_tarski(sK0,sK2) != sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_111])])).

fof(f1955,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK0,sK2)
    | ~ spl11_108
    | ~ spl11_111 ),
    inference(backward_demodulation,[],[f1902,f1905])).

fof(f1905,plain,
    ( k4_tarski(sK0,sK2) != sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_111 ),
    inference(avatar_component_clause,[],[f1904])).

fof(f2111,plain,
    ( ~ spl11_117
    | spl11_27
    | spl11_31
    | spl11_33 ),
    inference(avatar_split_clause,[],[f2014,f259,f253,f224,f2109])).

fof(f2109,plain,
    ( spl11_117
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_117])])).

fof(f224,plain,
    ( spl11_27
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f2014,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_27
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f264,f225])).

fof(f225,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK1))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f2089,plain,
    ( spl11_114
    | ~ spl11_90
    | ~ spl11_100
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f1992,f1901,f1843,f1717,f2087])).

fof(f2087,plain,
    ( spl11_114
  <=> r2_hidden(sK10(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).

fof(f1843,plain,
    ( spl11_100
  <=> r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f1992,plain,
    ( r2_hidden(sK10(sK1,sK1),sK1)
    | ~ spl11_90
    | ~ spl11_100
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1981,f1939])).

fof(f1939,plain,
    ( r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK1))),sK1)
    | ~ spl11_100
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1902,f1844])).

fof(f1844,plain,
    ( r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1)
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f1973,plain,(
    spl11_113 ),
    inference(avatar_contradiction_clause,[],[f1972])).

fof(f1972,plain,
    ( $false
    | ~ spl11_113 ),
    inference(subsumption_resolution,[],[f1971,f60])).

fof(f1971,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl11_113 ),
    inference(subsumption_resolution,[],[f1970,f56])).

fof(f1970,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl11_113 ),
    inference(resolution,[],[f1968,f49])).

fof(f1968,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_113 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f1967,plain,
    ( spl11_113
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_113])])).

fof(f1969,plain,
    ( ~ spl11_113
    | spl11_15
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f1911,f1901,f149,f1967])).

fof(f149,plain,
    ( spl11_15
  <=> ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1911,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_15
    | ~ spl11_108 ),
    inference(backward_demodulation,[],[f1902,f150])).

fof(f150,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1909,plain,
    ( spl11_108
    | spl11_110
    | spl11_3
    | spl11_15 ),
    inference(avatar_split_clause,[],[f1756,f149,f71,f1907,f1901])).

fof(f1907,plain,
    ( spl11_110
  <=> k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_110])])).

fof(f71,plain,
    ( spl11_3
  <=> k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1756,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | k4_tarski(sK0,sK1) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f1754,f72])).

fof(f72,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1754,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | k4_tarski(sK0,sK1) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_15 ),
    inference(resolution,[],[f150,f90])).

fof(f1891,plain,
    ( spl11_106
    | spl11_91
    | spl11_105 ),
    inference(avatar_split_clause,[],[f1890,f1871,f1714,f1874])).

fof(f1874,plain,
    ( spl11_106
  <=> r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f1714,plain,
    ( spl11_91
  <=> sK1 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_91])])).

fof(f1871,plain,
    ( spl11_105
  <=> ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_105])])).

fof(f1890,plain,
    ( r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1)
    | ~ spl11_91
    | ~ spl11_105 ),
    inference(subsumption_resolution,[],[f1886,f1715])).

fof(f1715,plain,
    ( sK1 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_91 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1886,plain,
    ( r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1)
    | sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_105 ),
    inference(resolution,[],[f1872,f42])).

fof(f1872,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_105 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1889,plain,
    ( spl11_91
    | spl11_105
    | spl11_107 ),
    inference(avatar_contradiction_clause,[],[f1888])).

fof(f1888,plain,
    ( $false
    | ~ spl11_91
    | ~ spl11_105
    | ~ spl11_107 ),
    inference(subsumption_resolution,[],[f1887,f1715])).

fof(f1887,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_105
    | ~ spl11_107 ),
    inference(subsumption_resolution,[],[f1886,f1878])).

fof(f1878,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1)
    | ~ spl11_107 ),
    inference(avatar_component_clause,[],[f1877])).

fof(f1877,plain,
    ( spl11_107
  <=> ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f1881,plain,
    ( spl11_100
    | spl11_91
    | spl11_103 ),
    inference(avatar_split_clause,[],[f1860,f1852,f1714,f1843])).

fof(f1852,plain,
    ( spl11_103
  <=> ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f1860,plain,
    ( r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1)
    | ~ spl11_91
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f1856,f1715])).

fof(f1856,plain,
    ( r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1)
    | sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_103 ),
    inference(resolution,[],[f1853,f42])).

fof(f1853,plain,
    ( ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_103 ),
    inference(avatar_component_clause,[],[f1852])).

fof(f1879,plain,
    ( ~ spl11_105
    | ~ spl11_107
    | spl11_91 ),
    inference(avatar_split_clause,[],[f1790,f1714,f1877,f1871])).

fof(f1790,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK1)
    | ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK1),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_91 ),
    inference(extensionality_resolution,[],[f43,f1715])).

fof(f1861,plain,
    ( spl11_98
    | spl11_89
    | spl11_97 ),
    inference(avatar_split_clause,[],[f1830,f1816,f1708,f1819])).

fof(f1819,plain,
    ( spl11_98
  <=> r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f1708,plain,
    ( spl11_89
  <=> sK2 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f1816,plain,
    ( spl11_97
  <=> ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_97])])).

fof(f1830,plain,
    ( r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2)
    | ~ spl11_89
    | ~ spl11_97 ),
    inference(subsumption_resolution,[],[f1826,f1709])).

fof(f1709,plain,
    ( sK2 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_89 ),
    inference(avatar_component_clause,[],[f1708])).

fof(f1826,plain,
    ( r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2)
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_97 ),
    inference(resolution,[],[f1817,f42])).

fof(f1817,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_97 ),
    inference(avatar_component_clause,[],[f1816])).

fof(f1859,plain,
    ( spl11_91
    | spl11_101
    | spl11_103 ),
    inference(avatar_contradiction_clause,[],[f1858])).

fof(f1858,plain,
    ( $false
    | ~ spl11_91
    | ~ spl11_101
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f1857,f1715])).

fof(f1857,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_101
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f1856,f1847])).

fof(f1847,plain,
    ( ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1)
    | ~ spl11_101 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f1846,plain,
    ( spl11_101
  <=> ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f1854,plain,
    ( ~ spl11_101
    | ~ spl11_103
    | spl11_91 ),
    inference(avatar_split_clause,[],[f1789,f1714,f1852,f1846])).

fof(f1789,plain,
    ( ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK1)
    | ~ spl11_91 ),
    inference(extensionality_resolution,[],[f43,f1715])).

fof(f1829,plain,
    ( spl11_89
    | spl11_97
    | spl11_99 ),
    inference(avatar_contradiction_clause,[],[f1828])).

fof(f1828,plain,
    ( $false
    | ~ spl11_89
    | ~ spl11_97
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f1827,f1709])).

fof(f1827,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_97
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f1826,f1823])).

fof(f1823,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2)
    | ~ spl11_99 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1822,plain,
    ( spl11_99
  <=> ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f1824,plain,
    ( ~ spl11_97
    | ~ spl11_99
    | spl11_89 ),
    inference(avatar_split_clause,[],[f1775,f1708,f1822,f1816])).

fof(f1775,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK2)
    | ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK2),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_89 ),
    inference(extensionality_resolution,[],[f43,f1709])).

fof(f1795,plain,
    ( spl11_89
    | spl11_93
    | spl11_95 ),
    inference(avatar_contradiction_clause,[],[f1794])).

fof(f1794,plain,
    ( $false
    | ~ spl11_89
    | ~ spl11_93
    | ~ spl11_95 ),
    inference(subsumption_resolution,[],[f1793,f1709])).

fof(f1793,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_93
    | ~ spl11_95 ),
    inference(subsumption_resolution,[],[f1792,f1781])).

fof(f1781,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK2)
    | ~ spl11_93 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1780,plain,
    ( spl11_93
  <=> ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f1792,plain,
    ( r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK2)
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_95 ),
    inference(resolution,[],[f1787,f42])).

fof(f1787,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ spl11_95 ),
    inference(avatar_component_clause,[],[f1786])).

fof(f1786,plain,
    ( spl11_95
  <=> ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f1788,plain,
    ( ~ spl11_93
    | ~ spl11_95
    | spl11_89 ),
    inference(avatar_split_clause,[],[f1774,f1708,f1786,f1780])).

fof(f1774,plain,
    ( ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))))
    | ~ r2_hidden(sK10(sK2,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))),sK2)
    | ~ spl11_89 ),
    inference(extensionality_resolution,[],[f43,f1709])).

fof(f1762,plain,
    ( ~ spl11_13
    | ~ spl11_15
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1403,f71,f149,f143])).

fof(f1403,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_3 ),
    inference(extensionality_resolution,[],[f43,f72])).

fof(f1742,plain,
    ( spl11_13
    | ~ spl11_58
    | ~ spl11_88 ),
    inference(avatar_contradiction_clause,[],[f1741])).

fof(f1741,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_58
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f1730,f54])).

fof(f1730,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_13
    | ~ spl11_58
    | ~ spl11_88 ),
    inference(backward_demodulation,[],[f1720,f144])).

fof(f1720,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_58
    | ~ spl11_88 ),
    inference(backward_demodulation,[],[f1712,f477])).

fof(f1712,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f1711])).

fof(f1711,plain,
    ( spl11_88
  <=> sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f1719,plain,
    ( spl11_88
    | spl11_90
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f585,f146,f1717,f1711])).

fof(f146,plain,
    ( spl11_14
  <=> r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f585,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_14 ),
    inference(resolution,[],[f83,f147])).

fof(f147,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f83,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X7,k2_zfmisc_1(X5,k2_tarski(X6,X4)))
      | sK5(X5,k2_tarski(X6,X4),X7) = X6
      | sK5(X5,k2_tarski(X6,X4),X7) = X4 ) ),
    inference(resolution,[],[f57,f51])).

fof(f1671,plain,
    ( spl11_86
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f1139,f401,f119,f1669])).

fof(f1669,plain,
    ( spl11_86
  <=> r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f119,plain,
    ( spl11_8
  <=> r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f401,plain,
    ( spl11_50
  <=> k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),sK2) = sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1139,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),k2_tarski(sK0,sK1))
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(resolution,[],[f424,f120])).

fof(f120,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f424,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(X13,X14))
        | r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),X13) )
    | ~ spl11_50 ),
    inference(superposition,[],[f45,f402])).

fof(f402,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),sK2) = sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f401])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',l54_zfmisc_1)).

fof(f1655,plain,
    ( spl11_84
    | ~ spl11_6
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f1136,f394,f106,f1653])).

fof(f1653,plain,
    ( spl11_84
  <=> r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f1136,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),k2_tarski(sK0,sK1))
    | ~ spl11_6
    | ~ spl11_48 ),
    inference(resolution,[],[f409,f107])).

fof(f409,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(X13,X14))
        | r2_hidden(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),X13) )
    | ~ spl11_48 ),
    inference(superposition,[],[f45,f395])).

fof(f1411,plain,
    ( spl11_78
    | spl11_76
    | spl11_75 ),
    inference(avatar_split_clause,[],[f1165,f1156,f1159,f1363])).

fof(f1363,plain,
    ( spl11_78
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f1159,plain,
    ( spl11_76
  <=> r2_hidden(sK10(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f1156,plain,
    ( spl11_75
  <=> ~ r2_hidden(sK10(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f1165,plain,
    ( r2_hidden(sK10(sK1,sK2),sK1)
    | sK1 = sK2
    | ~ spl11_75 ),
    inference(resolution,[],[f1157,f42])).

fof(f1157,plain,
    ( ~ r2_hidden(sK10(sK1,sK2),sK2)
    | ~ spl11_75 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1400,plain,
    ( spl11_80
    | spl11_79
    | spl11_83 ),
    inference(avatar_split_clause,[],[f1397,f1387,f1366,f1378])).

fof(f1378,plain,
    ( spl11_80
  <=> r2_hidden(sK10(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f1366,plain,
    ( spl11_79
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f1387,plain,
    ( spl11_83
  <=> ~ r2_hidden(sK10(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f1397,plain,
    ( r2_hidden(sK10(sK2,sK1),sK1)
    | ~ spl11_79
    | ~ spl11_83 ),
    inference(subsumption_resolution,[],[f1393,f1367])).

fof(f1367,plain,
    ( sK1 != sK2
    | ~ spl11_79 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f1393,plain,
    ( r2_hidden(sK10(sK2,sK1),sK1)
    | sK1 = sK2
    | ~ spl11_83 ),
    inference(resolution,[],[f1388,f42])).

fof(f1388,plain,
    ( ~ r2_hidden(sK10(sK2,sK1),sK2)
    | ~ spl11_83 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1396,plain,
    ( spl11_79
    | spl11_81
    | spl11_83 ),
    inference(avatar_contradiction_clause,[],[f1395])).

fof(f1395,plain,
    ( $false
    | ~ spl11_79
    | ~ spl11_81
    | ~ spl11_83 ),
    inference(subsumption_resolution,[],[f1394,f1367])).

fof(f1394,plain,
    ( sK1 = sK2
    | ~ spl11_81
    | ~ spl11_83 ),
    inference(subsumption_resolution,[],[f1393,f1382])).

fof(f1382,plain,
    ( ~ r2_hidden(sK10(sK2,sK1),sK1)
    | ~ spl11_81 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f1381,plain,
    ( spl11_81
  <=> ~ r2_hidden(sK10(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f1389,plain,
    ( ~ spl11_81
    | ~ spl11_83
    | ~ spl11_66
    | spl11_73 ),
    inference(avatar_split_clause,[],[f1151,f1130,f729,f1387,f1381])).

fof(f729,plain,
    ( spl11_66
  <=> sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f1130,plain,
    ( spl11_73
  <=> sK1 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f1151,plain,
    ( ~ r2_hidden(sK10(sK2,sK1),sK2)
    | ~ r2_hidden(sK10(sK2,sK1),sK1)
    | ~ spl11_66
    | ~ spl11_73 ),
    inference(forward_demodulation,[],[f1150,f730])).

fof(f730,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f729])).

fof(f1150,plain,
    ( ~ r2_hidden(sK10(sK2,sK1),sK1)
    | ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK1),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ spl11_66
    | ~ spl11_73 ),
    inference(forward_demodulation,[],[f1146,f730])).

fof(f1146,plain,
    ( ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK1),sK1)
    | ~ r2_hidden(sK10(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK1),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ spl11_73 ),
    inference(extensionality_resolution,[],[f43,f1131])).

fof(f1131,plain,
    ( sK1 != sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | ~ spl11_73 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1368,plain,
    ( ~ spl11_79
    | ~ spl11_66
    | spl11_73 ),
    inference(avatar_split_clause,[],[f1147,f1130,f729,f1366])).

fof(f1147,plain,
    ( sK1 != sK2
    | ~ spl11_66
    | ~ spl11_73 ),
    inference(superposition,[],[f1131,f730])).

fof(f1352,plain,
    ( ~ spl11_16
    | spl11_21
    | ~ spl11_60
    | spl11_75
    | spl11_77 ),
    inference(avatar_contradiction_clause,[],[f1351])).

fof(f1351,plain,
    ( $false
    | ~ spl11_16
    | ~ spl11_21
    | ~ spl11_60
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1350,f1179])).

fof(f1179,plain,
    ( k4_tarski(sK0,sK1) != sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl11_21
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f187])).

fof(f187,plain,
    ( k4_tarski(sK0,sK1) != sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl11_21
  <=> k4_tarski(sK0,sK1) != sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f1166,plain,
    ( sK1 = sK2
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1165,f1163])).

fof(f1163,plain,
    ( ~ r2_hidden(sK10(sK1,sK2),sK1)
    | ~ spl11_77 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1162,plain,
    ( spl11_77
  <=> ~ r2_hidden(sK10(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f1350,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl11_16
    | ~ spl11_60
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1344,f1208])).

fof(f1208,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))))) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl11_60
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f484])).

fof(f484,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl11_60
  <=> k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f1344,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))))
    | ~ spl11_16
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(duplicate_literal_removal,[],[f1343])).

fof(f1343,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))))
    | sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))))
    | ~ spl11_16
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(forward_demodulation,[],[f1222,f1166])).

fof(f1222,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))))
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_16
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f586])).

fof(f586,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_16 ),
    inference(resolution,[],[f83,f160])).

fof(f160,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_16
  <=> r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1340,plain,
    ( spl11_13
    | ~ spl11_14
    | ~ spl11_58
    | spl11_75
    | spl11_77 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_58
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1330,f54])).

fof(f1330,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_58
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1329,f1175])).

fof(f1175,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl11_13
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f144])).

fof(f1329,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)))
    | ~ spl11_14
    | ~ spl11_58
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1323,f1207])).

fof(f1207,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))))) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1)))
    | ~ spl11_58
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f477])).

fof(f1323,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))))
    | ~ spl11_14
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(duplicate_literal_removal,[],[f1322])).

fof(f1322,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))))
    | sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))))
    | ~ spl11_14
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(forward_demodulation,[],[f1221,f1166])).

fof(f1221,plain,
    ( sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK1),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK1))))
    | sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_14
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(backward_demodulation,[],[f1166,f585])).

fof(f1168,plain,
    ( ~ spl11_66
    | spl11_73
    | spl11_75
    | spl11_77 ),
    inference(avatar_contradiction_clause,[],[f1167])).

fof(f1167,plain,
    ( $false
    | ~ spl11_66
    | ~ spl11_73
    | ~ spl11_75
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1166,f1147])).

fof(f1164,plain,
    ( ~ spl11_75
    | ~ spl11_77
    | ~ spl11_66
    | spl11_73 ),
    inference(avatar_split_clause,[],[f1149,f1130,f729,f1162,f1156])).

fof(f1149,plain,
    ( ~ r2_hidden(sK10(sK1,sK2),sK1)
    | ~ r2_hidden(sK10(sK1,sK2),sK2)
    | ~ spl11_66
    | ~ spl11_73 ),
    inference(forward_demodulation,[],[f1148,f730])).

fof(f1148,plain,
    ( ~ r2_hidden(sK10(sK1,sK2),sK2)
    | ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))),sK1)
    | ~ spl11_66
    | ~ spl11_73 ),
    inference(forward_demodulation,[],[f1145,f730])).

fof(f1145,plain,
    ( ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ r2_hidden(sK10(sK1,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))),sK1)
    | ~ spl11_73 ),
    inference(extensionality_resolution,[],[f43,f1131])).

fof(f1135,plain,
    ( spl11_72
    | spl11_66
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f510,f416,f729,f1133])).

fof(f1133,plain,
    ( spl11_72
  <=> sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f416,plain,
    ( spl11_52
  <=> r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f510,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | sK1 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | ~ spl11_52 ),
    inference(resolution,[],[f417,f57])).

fof(f417,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),k2_tarski(sK1,sK2))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f416])).

fof(f1084,plain,
    ( spl11_70
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f441,f159,f1082])).

fof(f1082,plain,
    ( spl11_70
  <=> sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f441,plain,
    ( sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_16 ),
    inference(resolution,[],[f80,f160])).

fof(f1077,plain,
    ( spl11_68
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f440,f146,f1075])).

fof(f440,plain,
    ( sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))
    | ~ spl11_14 ),
    inference(resolution,[],[f80,f147])).

fof(f787,plain,(
    ~ spl11_62 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | ~ spl11_62 ),
    inference(resolution,[],[f540,f60])).

fof(f540,plain,
    ( ! [X1] : ~ r2_hidden(sK0,X1)
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl11_62
  <=> ! [X1] : ~ r2_hidden(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f786,plain,(
    ~ spl11_62 ),
    inference(avatar_contradiction_clause,[],[f783])).

fof(f783,plain,
    ( $false
    | ~ spl11_62 ),
    inference(resolution,[],[f540,f54])).

fof(f785,plain,(
    ~ spl11_62 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl11_62 ),
    inference(resolution,[],[f540,f56])).

fof(f731,plain,
    ( spl11_66
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f644,f542,f729])).

fof(f542,plain,
    ( spl11_64
  <=> ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),X0)
        | ~ r2_hidden(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f644,plain,
    ( sK2 = sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | ~ spl11_64 ),
    inference(resolution,[],[f560,f60])).

fof(f560,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k1_tarski(X0))
        | sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)) = X0 )
    | ~ spl11_64 ),
    inference(resolution,[],[f543,f58])).

fof(f543,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),X0)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f542])).

fof(f544,plain,
    ( spl11_62
    | spl11_64
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f389,f377,f542,f539])).

fof(f377,plain,
    ( spl11_46
  <=> k4_tarski(sK0,sK2) = k4_tarski(sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),X0)
        | ~ r2_hidden(sK2,X0)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl11_46 ),
    inference(resolution,[],[f384,f49])).

fof(f384,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(X11,X12))
        | r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),X12) )
    | ~ spl11_46 ),
    inference(superposition,[],[f46,f378])).

fof(f378,plain,
    ( k4_tarski(sK0,sK2) = k4_tarski(sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f377])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f485,plain,
    ( spl11_60
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f449,f159,f483])).

fof(f449,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f441,f327])).

fof(f327,plain,
    ( k4_tarski(sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_16 ),
    inference(resolution,[],[f50,f160])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f478,plain,
    ( spl11_58
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f448,f146,f476])).

fof(f448,plain,
    ( k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f440,f325])).

fof(f325,plain,
    ( k4_tarski(sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))))) = sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_14 ),
    inference(resolution,[],[f50,f147])).

fof(f463,plain,
    ( spl11_56
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f428,f201,f461])).

fof(f461,plain,
    ( spl11_56
  <=> sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f201,plain,
    ( spl11_24
  <=> r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f428,plain,
    ( sK0 = sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))
    | ~ spl11_24 ),
    inference(resolution,[],[f80,f202])).

fof(f202,plain,
    ( r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f456,plain,
    ( spl11_54
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f447,f377,f201,f454])).

fof(f454,plain,
    ( spl11_54
  <=> k4_tarski(sK0,sK2) = k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f447,plain,
    ( k4_tarski(sK0,sK2) = k4_tarski(sK0,sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(backward_demodulation,[],[f428,f378])).

fof(f418,plain,
    ( spl11_52
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f388,f377,f201,f416])).

fof(f388,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),k2_tarski(sK1,sK2))
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(resolution,[],[f384,f202])).

fof(f403,plain,
    ( spl11_50
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f329,f119,f401])).

fof(f329,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),sK2) = sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_8 ),
    inference(forward_demodulation,[],[f326,f248])).

fof(f248,plain,
    ( sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))))
    | ~ spl11_8 ),
    inference(resolution,[],[f79,f120])).

fof(f326,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))))) = sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_8 ),
    inference(resolution,[],[f50,f120])).

fof(f396,plain,
    ( spl11_48
    | ~ spl11_6
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f328,f288,f106,f394])).

fof(f288,plain,
    ( spl11_38
  <=> sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f328,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK2) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_6
    | ~ spl11_38 ),
    inference(forward_demodulation,[],[f324,f289])).

fof(f289,plain,
    ( sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f288])).

fof(f324,plain,
    ( k4_tarski(sK4(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))),sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))) = sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_6 ),
    inference(resolution,[],[f50,f107])).

fof(f379,plain,
    ( spl11_46
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f318,f201,f377])).

fof(f318,plain,
    ( k4_tarski(sK0,sK2) = k4_tarski(sK4(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)),sK5(k1_tarski(sK0),k2_tarski(sK1,sK2),k4_tarski(sK0,sK2)))
    | ~ spl11_24 ),
    inference(resolution,[],[f50,f202])).

fof(f354,plain,
    ( spl11_44
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f248,f119,f352])).

fof(f352,plain,
    ( spl11_44
  <=> sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f330,plain,
    ( spl11_42
    | spl11_23
    | spl11_41 ),
    inference(avatar_split_clause,[],[f314,f300,f192,f303])).

fof(f314,plain,
    ( r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | ~ spl11_23
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f310,f193])).

fof(f310,plain,
    ( r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_41 ),
    inference(resolution,[],[f301,f42])).

fof(f313,plain,
    ( spl11_23
    | spl11_41
    | spl11_43 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl11_23
    | ~ spl11_41
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f311,f193])).

fof(f311,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_41
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f310,f307])).

fof(f307,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl11_43
  <=> ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f308,plain,
    ( ~ spl11_41
    | ~ spl11_43
    | spl11_23 ),
    inference(avatar_split_clause,[],[f234,f192,f306,f300])).

fof(f234,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),k4_tarski(sK0,sK2))
    | ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK2)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_23 ),
    inference(extensionality_resolution,[],[f43,f193])).

fof(f294,plain,
    ( spl11_23
    | spl11_35
    | spl11_37 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl11_23
    | ~ spl11_35
    | ~ spl11_37 ),
    inference(subsumption_resolution,[],[f292,f193])).

fof(f292,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_35
    | ~ spl11_37 ),
    inference(subsumption_resolution,[],[f291,f275])).

fof(f291,plain,
    ( r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_37 ),
    inference(resolution,[],[f281,f42])).

fof(f281,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl11_37
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f290,plain,
    ( spl11_38
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f247,f106,f288])).

fof(f247,plain,
    ( sK2 = sK5(k2_tarski(sK0,sK1),k1_tarski(sK2),sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))))
    | ~ spl11_6 ),
    inference(resolution,[],[f79,f107])).

fof(f282,plain,
    ( ~ spl11_35
    | ~ spl11_37
    | spl11_23 ),
    inference(avatar_split_clause,[],[f233,f192,f280,f274])).

fof(f233,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK2),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK2))
    | ~ spl11_23 ),
    inference(extensionality_resolution,[],[f43,f193])).

fof(f268,plain,
    ( spl11_32
    | spl11_21
    | spl11_31 ),
    inference(avatar_split_clause,[],[f267,f253,f186,f256])).

fof(f256,plain,
    ( spl11_32
  <=> r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f267,plain,
    ( r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ spl11_21
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f263,f187])).

fof(f266,plain,
    ( spl11_21
    | spl11_31
    | spl11_33 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl11_21
    | ~ spl11_31
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f264,f187])).

fof(f261,plain,
    ( ~ spl11_31
    | ~ spl11_33
    | spl11_21 ),
    inference(avatar_split_clause,[],[f218,f186,f259,f253])).

fof(f218,plain,
    ( ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),k4_tarski(sK0,sK1))
    | ~ r2_hidden(sK10(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k4_tarski(sK0,sK1)),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_21 ),
    inference(extensionality_resolution,[],[f43,f187])).

fof(f239,plain,
    ( spl11_21
    | spl11_27
    | spl11_29 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl11_21
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f237,f187])).

fof(f237,plain,
    ( k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f236,f225])).

fof(f236,plain,
    ( r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK1))
    | k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_29 ),
    inference(resolution,[],[f231,f42])).

fof(f231,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl11_29
  <=> ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f232,plain,
    ( ~ spl11_27
    | ~ spl11_29
    | spl11_21 ),
    inference(avatar_split_clause,[],[f217,f186,f230,f224])).

fof(f217,plain,
    ( ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))))
    | ~ r2_hidden(sK10(k4_tarski(sK0,sK1),sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))),k4_tarski(sK0,sK1))
    | ~ spl11_21 ),
    inference(extensionality_resolution,[],[f43,f187])).

fof(f213,plain,
    ( spl11_19
    | ~ spl11_22 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f211,f54])).

fof(f211,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(forward_demodulation,[],[f169,f196])).

fof(f196,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl11_22
  <=> k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f210,plain,(
    spl11_25 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f208,f60])).

fof(f208,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f207,f54])).

fof(f207,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl11_25 ),
    inference(resolution,[],[f205,f49])).

fof(f205,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl11_25
  <=> ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f206,plain,
    ( ~ spl11_25
    | spl11_17
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f199,f195,f162,f204])).

fof(f162,plain,
    ( spl11_17
  <=> ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f199,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_17
    | ~ spl11_22 ),
    inference(backward_demodulation,[],[f196,f163])).

fof(f163,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f197,plain,
    ( spl11_20
    | spl11_22
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f178,f165,f195,f189])).

fof(f189,plain,
    ( spl11_20
  <=> k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f165,plain,
    ( spl11_18
  <=> r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f178,plain,
    ( k4_tarski(sK0,sK2) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | k4_tarski(sK0,sK1) = sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_18 ),
    inference(resolution,[],[f166,f57])).

fof(f166,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f179,plain,
    ( spl11_14
    | spl11_3
    | spl11_13 ),
    inference(avatar_split_clause,[],[f157,f143,f71,f146])).

fof(f157,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_3
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f153,f72])).

fof(f153,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_13 ),
    inference(resolution,[],[f144,f42])).

fof(f176,plain,
    ( spl11_3
    | spl11_17
    | spl11_19 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_17
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f174,f72])).

fof(f174,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_17
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f173,f163])).

fof(f173,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_19 ),
    inference(resolution,[],[f169,f42])).

fof(f172,plain,
    ( spl11_8
    | spl11_1
    | spl11_11 ),
    inference(avatar_split_clause,[],[f138,f128,f65,f119])).

fof(f128,plain,
    ( spl11_11
  <=> ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f138,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_1
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f134,f66])).

fof(f134,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl11_11 ),
    inference(resolution,[],[f129,f42])).

fof(f129,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f170,plain,
    ( ~ spl11_17
    | ~ spl11_19
    | spl11_3 ),
    inference(avatar_split_clause,[],[f95,f71,f168,f162])).

fof(f95,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ r2_hidden(sK10(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl11_3 ),
    inference(extensionality_resolution,[],[f43,f72])).

fof(f156,plain,
    ( spl11_3
    | spl11_13
    | spl11_15 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f154,f72])).

fof(f154,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f153,f150])).

fof(f151,plain,
    ( ~ spl11_13
    | ~ spl11_15
    | spl11_3 ),
    inference(avatar_split_clause,[],[f94,f71,f149,f143])).

fof(f94,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)))
    | ~ spl11_3 ),
    inference(extensionality_resolution,[],[f43,f72])).

fof(f137,plain,
    ( spl11_1
    | spl11_9
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_9
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f135,f66])).

fof(f135,plain,
    ( k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl11_9
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f134,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl11_9
  <=> ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f132,plain,
    ( spl11_6
    | spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f117,f103,f65,f106])).

fof(f117,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f113,f66])).

fof(f113,plain,
    ( r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl11_5 ),
    inference(resolution,[],[f104,f42])).

fof(f130,plain,
    ( ~ spl11_9
    | ~ spl11_11
    | spl11_1 ),
    inference(avatar_split_clause,[],[f93,f65,f128,f122])).

fof(f93,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ r2_hidden(sK10(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ spl11_1 ),
    inference(extensionality_resolution,[],[f43,f66])).

fof(f116,plain,
    ( spl11_1
    | spl11_5
    | spl11_7 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f114,f66])).

fof(f114,plain,
    ( k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f113,f110])).

fof(f111,plain,
    ( ~ spl11_5
    | ~ spl11_7
    | spl11_1 ),
    inference(avatar_split_clause,[],[f92,f65,f109,f103])).

fof(f92,plain,
    ( ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)))
    | ~ r2_hidden(sK10(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)))
    | ~ spl11_1 ),
    inference(extensionality_resolution,[],[f43,f66])).

fof(f73,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f22,f71,f65])).

fof(f22,plain,
    ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) != k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) != k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
        & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t36_zfmisc_1.p',t36_zfmisc_1)).
%------------------------------------------------------------------------------
