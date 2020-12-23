%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:00 EST 2020

% Result     : Theorem 8.84s
% Output     : Refutation 9.00s
% Verified   : 
% Statistics : Number of formulae       :  280 ( 671 expanded)
%              Number of leaves         :   63 ( 323 expanded)
%              Depth                    :   12
%              Number of atoms          :  784 (1586 expanded)
%              Number of equality atoms :  194 ( 548 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f68,f75,f83,f89,f97,f103,f110,f121,f148,f160,f179,f189,f209,f297,f321,f325,f329,f339,f444,f461,f470,f488,f561,f565,f593,f641,f649,f864,f959,f963,f980,f1159,f1193,f1438,f1543,f1614,f1618,f4374,f5814,f6083,f6354,f6428,f7948,f11337,f14872,f14912,f19737])).

fof(f19737,plain,
    ( ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_45
    | spl3_69
    | ~ spl3_89
    | ~ spl3_90
    | ~ spl3_149
    | ~ spl3_202
    | ~ spl3_217
    | ~ spl3_227 ),
    inference(avatar_contradiction_clause,[],[f19736])).

fof(f19736,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_45
    | spl3_69
    | ~ spl3_89
    | ~ spl3_90
    | ~ spl3_149
    | ~ spl3_202
    | ~ spl3_217
    | ~ spl3_227 ),
    inference(subsumption_resolution,[],[f19735,f16635])).

fof(f16635,plain,
    ( ! [X42] : k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(X42,sK1),k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_89
    | ~ spl3_149
    | ~ spl3_202
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f16634,f188])).

fof(f188,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f16634,plain,
    ( ! [X42] : k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X42,sK1),k1_xboole_0),k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_89
    | ~ spl3_149
    | ~ spl3_202
    | ~ spl3_217 ),
    inference(forward_demodulation,[],[f16462,f13712])).

fof(f13712,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X15,X14)))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_89
    | ~ spl3_202 ),
    inference(backward_demodulation,[],[f2253,f13711])).

fof(f13711,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X11)))
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_202 ),
    inference(forward_demodulation,[],[f13220,f592])).

fof(f592,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl3_45
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f13220,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X11)
    | ~ spl3_30
    | ~ spl3_202 ),
    inference(superposition,[],[f11336,f328])).

fof(f328,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl3_30
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f11336,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl3_202 ),
    inference(avatar_component_clause,[],[f11335])).

fof(f11335,plain,
    ( spl3_202
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_202])])).

fof(f2253,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_45
    | ~ spl3_89 ),
    inference(forward_demodulation,[],[f2252,f793])).

fof(f793,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(X10,X11),X12)
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f738,f188])).

fof(f738,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0),X12)
    | ~ spl3_11
    | ~ spl3_45 ),
    inference(superposition,[],[f592,f109])).

fof(f109,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_11
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2252,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_45
    | ~ spl3_89 ),
    inference(forward_demodulation,[],[f2251,f188])).

fof(f2251,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_45
    | ~ spl3_89 ),
    inference(forward_demodulation,[],[f2145,f793])).

fof(f2145,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15))))
    | ~ spl3_11
    | ~ spl3_89 ),
    inference(superposition,[],[f1613,f109])).

fof(f1613,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1612,plain,
    ( spl3_89
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f16462,plain,
    ( ! [X42] : k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X42,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X42,sK2),k4_xboole_0(X42,sK1)))
    | ~ spl3_149
    | ~ spl3_217 ),
    inference(superposition,[],[f14871,f6427])).

fof(f6427,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_149 ),
    inference(avatar_component_clause,[],[f6426])).

fof(f6426,plain,
    ( spl3_149
  <=> ! [X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).

fof(f14871,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl3_217 ),
    inference(avatar_component_clause,[],[f14870])).

fof(f14870,plain,
    ( spl3_217
  <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).

fof(f19735,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_45
    | spl3_69
    | ~ spl3_89
    | ~ spl3_90
    | ~ spl3_227 ),
    inference(backward_demodulation,[],[f979,f19733])).

fof(f19733,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_89
    | ~ spl3_90
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f19732,f1710])).

fof(f1710,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,X31)))))
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1709,f592])).

fof(f1709,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,X31)))
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1708,f560])).

fof(f560,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl3_43
  <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1708,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k1_xboole_0),X31)))
    | ~ spl3_45
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1707,f592])).

fof(f1707,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,k1_xboole_0))),X31)
    | ~ spl3_45
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1668,f592])).

fof(f1668,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k1_xboole_0),X31)
    | ~ spl3_45
    | ~ spl3_90 ),
    inference(superposition,[],[f592,f1617])).

fof(f1617,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f1616])).

fof(f1616,plain,
    ( spl3_90
  <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f19732,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_89
    | ~ spl3_227 ),
    inference(forward_demodulation,[],[f18974,f430])).

fof(f430,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl3_11
    | ~ spl3_19
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f388,f188])).

fof(f388,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl3_11
    | ~ spl3_30 ),
    inference(superposition,[],[f328,f109])).

fof(f18974,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X26,X27))))))
    | ~ spl3_89
    | ~ spl3_227 ),
    inference(superposition,[],[f14911,f1613])).

fof(f14911,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12))))
    | ~ spl3_227 ),
    inference(avatar_component_clause,[],[f14910])).

fof(f14910,plain,
    ( spl3_227
  <=> ! [X11,X10,X12] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_227])])).

fof(f979,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))
    | spl3_69 ),
    inference(avatar_component_clause,[],[f977])).

fof(f977,plain,
    ( spl3_69
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f14912,plain,
    ( spl3_227
    | ~ spl3_29
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_164
    | ~ spl3_202 ),
    inference(avatar_split_clause,[],[f14046,f11335,f7946,f591,f327,f323,f14910])).

fof(f323,plain,
    ( spl3_29
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f7946,plain,
    ( spl3_164
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).

fof(f14046,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12))))
    | ~ spl3_29
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_164
    | ~ spl3_202 ),
    inference(backward_demodulation,[],[f821,f14043])).

fof(f14043,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(X214,X215)) = k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))
    | ~ spl3_29
    | ~ spl3_45
    | ~ spl3_164
    | ~ spl3_202 ),
    inference(forward_demodulation,[],[f14042,f13978])).

fof(f13978,plain,
    ( ! [X30,X31,X32] : k4_xboole_0(X30,k4_xboole_0(X31,X32)) = k5_xboole_0(X30,k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X30,X32))))
    | ~ spl3_29
    | ~ spl3_45
    | ~ spl3_202 ),
    inference(forward_demodulation,[],[f13309,f592])).

fof(f13309,plain,
    ( ! [X30,X31,X32] : k4_xboole_0(X30,k4_xboole_0(X31,X32)) = k5_xboole_0(X30,k4_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,X30)),X32))
    | ~ spl3_29
    | ~ spl3_202 ),
    inference(superposition,[],[f324,f11336])).

fof(f324,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f323])).

fof(f14042,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215)))) = k5_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))
    | ~ spl3_45
    | ~ spl3_164
    | ~ spl3_202 ),
    inference(forward_demodulation,[],[f13357,f592])).

fof(f13357,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215)) = k5_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215))
    | ~ spl3_164
    | ~ spl3_202 ),
    inference(superposition,[],[f7947,f11336])).

fof(f7947,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_164 ),
    inference(avatar_component_clause,[],[f7946])).

fof(f821,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))))))
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f761,f592])).

fof(f761,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12))))
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(superposition,[],[f592,f328])).

fof(f14872,plain,
    ( spl3_217
    | ~ spl3_74
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f5443,f4372,f1191,f14870])).

fof(f1191,plain,
    ( spl3_74
  <=> ! [X5,X4] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f4372,plain,
    ( spl3_134
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).

fof(f5443,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl3_74
    | ~ spl3_134 ),
    inference(superposition,[],[f1192,f4373])).

fof(f4373,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_134 ),
    inference(avatar_component_clause,[],[f4372])).

fof(f1192,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f1191])).

fof(f11337,plain,
    ( spl3_202
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f751,f591,f327,f11335])).

fof(f751,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(superposition,[],[f592,f328])).

fof(f7948,plain,
    ( spl3_164
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f1111,f961,f563,f323,f54,f7946])).

fof(f54,plain,
    ( spl3_2
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f563,plain,
    ( spl3_44
  <=> ! [X15] : k1_xboole_0 = k5_xboole_0(X15,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f961,plain,
    ( spl3_65
  <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1111,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f1073,f1100])).

fof(f1100,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_2
    | ~ spl3_44
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f1072,f55])).

fof(f55,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1072,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_44
    | ~ spl3_65 ),
    inference(superposition,[],[f962,f564])).

fof(f564,plain,
    ( ! [X15] : k1_xboole_0 = k5_xboole_0(X15,X15)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f563])).

fof(f962,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f961])).

fof(f1073,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_29
    | ~ spl3_65 ),
    inference(superposition,[],[f962,f324])).

fof(f6428,plain,
    ( spl3_149
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_148 ),
    inference(avatar_split_clause,[],[f6392,f6352,f295,f187,f119,f6426])).

fof(f119,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f295,plain,
    ( spl3_27
  <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f6352,plain,
    ( spl3_148
  <=> ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).

fof(f6392,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2))
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f6391,f296])).

fof(f296,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f295])).

fof(f6391,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)))
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f6361,f188])).

fof(f6361,plain,
    ( ! [X9] : k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k1_xboole_0))
    | ~ spl3_12
    | ~ spl3_148 ),
    inference(resolution,[],[f6353,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f6353,plain,
    ( ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0)
    | ~ spl3_148 ),
    inference(avatar_component_clause,[],[f6352])).

fof(f6354,plain,
    ( spl3_148
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_45
    | ~ spl3_84
    | ~ spl3_89
    | ~ spl3_146 ),
    inference(avatar_split_clause,[],[f6334,f6081,f1612,f1541,f591,f187,f176,f108,f6352])).

fof(f176,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1541,plain,
    ( spl3_84
  <=> ! [X8] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f6081,plain,
    ( spl3_146
  <=> ! [X53,X52] : r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).

fof(f6334,plain,
    ( ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_45
    | ~ spl3_84
    | ~ spl3_89
    | ~ spl3_146 ),
    inference(forward_demodulation,[],[f6333,f2253])).

fof(f6333,plain,
    ( ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(k4_xboole_0(X46,sK1),sK2)),k1_xboole_0)
    | ~ spl3_18
    | ~ spl3_84
    | ~ spl3_146 ),
    inference(forward_demodulation,[],[f6179,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f6179,plain,
    ( ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(k4_xboole_0(X46,sK1),sK2)),k4_xboole_0(sK2,sK2))
    | ~ spl3_84
    | ~ spl3_146 ),
    inference(superposition,[],[f6082,f1542])).

fof(f1542,plain,
    ( ! [X8] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f6082,plain,
    ( ! [X52,X53] : r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52)))
    | ~ spl3_146 ),
    inference(avatar_component_clause,[],[f6081])).

fof(f6083,plain,
    ( spl3_146
    | ~ spl3_61
    | ~ spl3_145 ),
    inference(avatar_split_clause,[],[f5898,f5812,f862,f6081])).

fof(f862,plain,
    ( spl3_61
  <=> ! [X5,X6] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f5812,plain,
    ( spl3_145
  <=> ! [X16,X17] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).

fof(f5898,plain,
    ( ! [X52,X53] : r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52)))
    | ~ spl3_61
    | ~ spl3_145 ),
    inference(superposition,[],[f863,f5813])).

fof(f5813,plain,
    ( ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16)
    | ~ spl3_145 ),
    inference(avatar_component_clause,[],[f5812])).

fof(f863,plain,
    ( ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f862])).

fof(f5814,plain,
    ( spl3_145
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_90
    | ~ spl3_134 ),
    inference(avatar_split_clause,[],[f5467,f4372,f1616,f591,f559,f5812])).

fof(f5467,plain,
    ( ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16)
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_90
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f5466,f4373])).

fof(f5466,plain,
    ( ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17)))
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_90
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f5465,f560])).

fof(f5465,plain,
    ( ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k1_xboole_0))))
    | ~ spl3_45
    | ~ spl3_90
    | ~ spl3_134 ),
    inference(forward_demodulation,[],[f5399,f592])).

fof(f5399,plain,
    ( ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k1_xboole_0))
    | ~ spl3_90
    | ~ spl3_134 ),
    inference(superposition,[],[f4373,f1617])).

fof(f4374,plain,
    ( spl3_134
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f402,f327,f323,f4372])).

fof(f402,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(superposition,[],[f324,f328])).

fof(f1618,plain,
    ( spl3_90
    | ~ spl3_11
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f406,f327,f108,f1616])).

fof(f406,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)
    | ~ spl3_11
    | ~ spl3_30 ),
    inference(superposition,[],[f109,f328])).

fof(f1614,plain,(
    spl3_89 ),
    inference(avatar_split_clause,[],[f47,f1612])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f35,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f36,f30,f30,f30,f30])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1543,plain,
    ( spl3_84
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1532,f1436,f323,f54,f1541])).

fof(f1436,plain,
    ( spl3_83
  <=> ! [X9] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f1532,plain,
    ( ! [X8] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f1507,f55])).

fof(f1507,plain,
    ( ! [X8] : k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))
    | ~ spl3_29
    | ~ spl3_83 ),
    inference(superposition,[],[f324,f1437])).

fof(f1437,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1438,plain,
    ( spl3_83
    | ~ spl3_45
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f760,f639,f591,f1436])).

fof(f639,plain,
    ( spl3_51
  <=> ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f760,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))
    | ~ spl3_45
    | ~ spl3_51 ),
    inference(superposition,[],[f592,f640])).

fof(f640,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f639])).

fof(f1193,plain,
    ( spl3_74
    | ~ spl3_2
    | ~ spl3_64
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f1181,f1157,f957,f54,f1191])).

fof(f957,plain,
    ( spl3_64
  <=> ! [X3,X2] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1157,plain,
    ( spl3_73
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f1181,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4
    | ~ spl3_2
    | ~ spl3_64
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1163,f55])).

fof(f1163,plain,
    ( ! [X4,X5] : k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5))
    | ~ spl3_64
    | ~ spl3_73 ),
    inference(superposition,[],[f1158,f958])).

fof(f958,plain,
    ( ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f957])).

fof(f1158,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1159,plain,
    ( spl3_73
    | ~ spl3_2
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_53
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f1109,f961,f647,f563,f319,f54,f1157])).

fof(f319,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f647,plain,
    ( spl3_53
  <=> ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f1109,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl3_2
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_53
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f1103,f1100])).

fof(f1103,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))
    | ~ spl3_2
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_53
    | ~ spl3_65 ),
    inference(backward_demodulation,[],[f701,f1100])).

fof(f701,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))
    | ~ spl3_28
    | ~ spl3_53 ),
    inference(superposition,[],[f320,f648])).

fof(f648,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f647])).

fof(f320,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f319])).

fof(f980,plain,(
    ~ spl3_69 ),
    inference(avatar_split_clause,[],[f46,f977])).

fof(f46,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f39,f43])).

fof(f39,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f963,plain,
    ( spl3_65
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f587,f563,f319,f961])).

fof(f587,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(superposition,[],[f320,f564])).

fof(f959,plain,
    ( spl3_64
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f586,f563,f319,f957])).

fof(f586,plain,
    ( ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))
    | ~ spl3_28
    | ~ spl3_44 ),
    inference(superposition,[],[f564,f320])).

fof(f864,plain,
    ( spl3_61
    | ~ spl3_3
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f404,f327,f58,f862])).

fof(f58,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f404,plain,
    ( ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)
    | ~ spl3_3
    | ~ spl3_30 ),
    inference(superposition,[],[f59,f328])).

fof(f59,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f649,plain,
    ( spl3_53
    | ~ spl3_31
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f585,f563,f337,f647])).

fof(f337,plain,
    ( spl3_31
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f585,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)
    | ~ spl3_31
    | ~ spl3_44 ),
    inference(superposition,[],[f564,f338])).

fof(f338,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f337])).

fof(f641,plain,
    ( spl3_51
    | ~ spl3_5
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f472,f468,f66,f639])).

fof(f66,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f468,plain,
    ( spl3_36
  <=> ! [X1] : r1_tarski(k4_xboole_0(sK2,X1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f472,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1)
    | ~ spl3_5
    | ~ spl3_36 ),
    inference(resolution,[],[f469,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f469,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(sK2,X1),sK1)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f468])).

fof(f593,plain,(
    spl3_45 ),
    inference(avatar_split_clause,[],[f43,f591])).

fof(f565,plain,
    ( spl3_44
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f527,f486,f323,f54,f563])).

fof(f486,plain,
    ( spl3_38
  <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f527,plain,
    ( ! [X15] : k1_xboole_0 = k5_xboole_0(X15,X15)
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f519,f522])).

fof(f522,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f508,f55])).

fof(f508,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(superposition,[],[f324,f487])).

fof(f487,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f486])).

fof(f519,plain,
    ( ! [X15] : k1_xboole_0 = k5_xboole_0(X15,k4_xboole_0(X15,k1_xboole_0))
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(superposition,[],[f324,f487])).

fof(f561,plain,
    ( spl3_43
    | ~ spl3_2
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f522,f486,f323,f54,f559])).

fof(f488,plain,
    ( spl3_38
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f432,f327,f207,f100,f486])).

fof(f100,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f207,plain,
    ( spl3_20
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f432,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f390,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f390,plain,
    ( ! [X10] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(superposition,[],[f328,f208])).

fof(f208,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f470,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f463,f459,f58,f468])).

fof(f459,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f463,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(sK2,X1),sK1)
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(resolution,[],[f460,f59])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK1) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f459])).

fof(f461,plain,
    ( spl3_35
    | ~ spl3_15
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f446,f441,f146,f459])).

fof(f146,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f441,plain,
    ( spl3_34
  <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK1) )
    | ~ spl3_15
    | ~ spl3_34 ),
    inference(superposition,[],[f147,f443])).

fof(f443,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f441])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
        | r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f444,plain,
    ( spl3_34
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f433,f327,f157,f72,f441])).

fof(f72,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f157,plain,
    ( spl3_16
  <=> sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f433,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f391,f159])).

fof(f159,plain,
    ( sK2 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f391,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_30 ),
    inference(superposition,[],[f328,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f339,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f330,f319,f54,f337])).

fof(f330,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(superposition,[],[f320,f55])).

fof(f329,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f41,f327])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f30,f30])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f325,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f38,f323])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f321,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f34,f319])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f297,plain,
    ( spl3_27
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f202,f187,f108,f295])).

fof(f202,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(superposition,[],[f109,f188])).

fof(f209,plain,
    ( spl3_20
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f198,f187,f108,f207])).

fof(f198,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(superposition,[],[f188,f109])).

fof(f189,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f155,f119,f108,f58,f187])).

fof(f155,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f150,f109])).

fof(f150,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f59])).

fof(f179,plain,
    ( spl3_18
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f163,f157,f108,f176])).

fof(f163,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f109,f159])).

fof(f160,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f154,f119,f72,f49,f157])).

fof(f49,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f154,plain,
    ( sK2 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f149,f74])).

fof(f149,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f51])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f148,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f45,f146])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f121,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f42,f119])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f110,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f70,f66,f58,f108])).

fof(f70,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f67,f59])).

fof(f103,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f94,f66,f100])).

fof(f94,plain,
    ( spl3_9
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f98,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f86,f58,f94])).

fof(f86,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f59,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f80,f66,f86])).

fof(f80,plain,
    ( spl3_7
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f82,f67])).

fof(f82,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f77,f72,f58,f80])).

fof(f77,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f59,f74])).

fof(f75,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f66,f49,f72])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f67,f51])).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:00:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (13945)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (13956)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (13943)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (13942)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (13957)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (13953)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (13946)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (13959)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (13955)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (13950)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (13947)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (13952)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (13944)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (13958)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (13951)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (13949)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (13948)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (13954)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 4.49/1.02  % (13946)Time limit reached!
% 4.49/1.02  % (13946)------------------------------
% 4.49/1.02  % (13946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.34/1.03  % (13946)Termination reason: Time limit
% 5.34/1.03  % (13946)Termination phase: Saturation
% 5.34/1.03  
% 5.34/1.03  % (13946)Memory used [KB]: 16502
% 5.34/1.03  % (13946)Time elapsed: 0.600 s
% 5.34/1.03  % (13946)------------------------------
% 5.34/1.03  % (13946)------------------------------
% 8.84/1.47  % (13949)Refutation found. Thanks to Tanya!
% 8.84/1.47  % SZS status Theorem for theBenchmark
% 8.84/1.48  % SZS output start Proof for theBenchmark
% 8.84/1.48  fof(f20415,plain,(
% 8.84/1.48    $false),
% 8.84/1.48    inference(avatar_sat_refutation,[],[f52,f56,f60,f68,f75,f83,f89,f97,f103,f110,f121,f148,f160,f179,f189,f209,f297,f321,f325,f329,f339,f444,f461,f470,f488,f561,f565,f593,f641,f649,f864,f959,f963,f980,f1159,f1193,f1438,f1543,f1614,f1618,f4374,f5814,f6083,f6354,f6428,f7948,f11337,f14872,f14912,f19737])).
% 8.84/1.48  fof(f19737,plain,(
% 8.84/1.48    ~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_43 | ~spl3_45 | spl3_69 | ~spl3_89 | ~spl3_90 | ~spl3_149 | ~spl3_202 | ~spl3_217 | ~spl3_227),
% 8.84/1.48    inference(avatar_contradiction_clause,[],[f19736])).
% 8.84/1.48  fof(f19736,plain,(
% 8.84/1.48    $false | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_43 | ~spl3_45 | spl3_69 | ~spl3_89 | ~spl3_90 | ~spl3_149 | ~spl3_202 | ~spl3_217 | ~spl3_227)),
% 8.84/1.48    inference(subsumption_resolution,[],[f19735,f16635])).
% 8.84/1.48  fof(f16635,plain,(
% 8.84/1.48    ( ! [X42] : (k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(X42,sK1),k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(sK1,sK2))))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_45 | ~spl3_89 | ~spl3_149 | ~spl3_202 | ~spl3_217)),
% 8.84/1.48    inference(forward_demodulation,[],[f16634,f188])).
% 8.84/1.48  fof(f188,plain,(
% 8.84/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | ~spl3_19),
% 8.84/1.48    inference(avatar_component_clause,[],[f187])).
% 8.84/1.48  fof(f187,plain,(
% 8.84/1.48    spl3_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),
% 8.84/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 9.00/1.48  fof(f16634,plain,(
% 9.00/1.48    ( ! [X42] : (k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X42,sK1),k1_xboole_0),k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(sK1,sK2))))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_45 | ~spl3_89 | ~spl3_149 | ~spl3_202 | ~spl3_217)),
% 9.00/1.48    inference(forward_demodulation,[],[f16462,f13712])).
% 9.00/1.48  fof(f13712,plain,(
% 9.00/1.48    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X15,X14)))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_45 | ~spl3_89 | ~spl3_202)),
% 9.00/1.48    inference(backward_demodulation,[],[f2253,f13711])).
% 9.00/1.48  fof(f13711,plain,(
% 9.00/1.48    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X11)))) ) | (~spl3_30 | ~spl3_45 | ~spl3_202)),
% 9.00/1.48    inference(forward_demodulation,[],[f13220,f592])).
% 9.00/1.48  fof(f592,plain,(
% 9.00/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_45),
% 9.00/1.48    inference(avatar_component_clause,[],[f591])).
% 9.00/1.48  fof(f591,plain,(
% 9.00/1.48    spl3_45 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 9.00/1.48  fof(f13220,plain,(
% 9.00/1.48    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X11)) ) | (~spl3_30 | ~spl3_202)),
% 9.00/1.48    inference(superposition,[],[f11336,f328])).
% 9.00/1.48  fof(f328,plain,(
% 9.00/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_30),
% 9.00/1.48    inference(avatar_component_clause,[],[f327])).
% 9.00/1.48  fof(f327,plain,(
% 9.00/1.48    spl3_30 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 9.00/1.48  fof(f11336,plain,(
% 9.00/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | ~spl3_202),
% 9.00/1.48    inference(avatar_component_clause,[],[f11335])).
% 9.00/1.48  fof(f11335,plain,(
% 9.00/1.48    spl3_202 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_202])])).
% 9.00/1.48  fof(f2253,plain,(
% 9.00/1.48    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_19 | ~spl3_45 | ~spl3_89)),
% 9.00/1.48    inference(forward_demodulation,[],[f2252,f793])).
% 9.00/1.48  fof(f793,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(X10,X11),X12)) ) | (~spl3_11 | ~spl3_19 | ~spl3_45)),
% 9.00/1.48    inference(forward_demodulation,[],[f738,f188])).
% 9.00/1.48  fof(f738,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0),X12)) ) | (~spl3_11 | ~spl3_45)),
% 9.00/1.48    inference(superposition,[],[f592,f109])).
% 9.00/1.48  fof(f109,plain,(
% 9.00/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_11),
% 9.00/1.48    inference(avatar_component_clause,[],[f108])).
% 9.00/1.48  fof(f108,plain,(
% 9.00/1.48    spl3_11 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 9.00/1.48  fof(f2252,plain,(
% 9.00/1.48    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_19 | ~spl3_45 | ~spl3_89)),
% 9.00/1.48    inference(forward_demodulation,[],[f2251,f188])).
% 9.00/1.48  fof(f2251,plain,(
% 9.00/1.48    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_19 | ~spl3_45 | ~spl3_89)),
% 9.00/1.48    inference(forward_demodulation,[],[f2145,f793])).
% 9.00/1.48  fof(f2145,plain,(
% 9.00/1.48    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15))))) ) | (~spl3_11 | ~spl3_89)),
% 9.00/1.48    inference(superposition,[],[f1613,f109])).
% 9.00/1.48  fof(f1613,plain,(
% 9.00/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ) | ~spl3_89),
% 9.00/1.48    inference(avatar_component_clause,[],[f1612])).
% 9.00/1.48  fof(f1612,plain,(
% 9.00/1.48    spl3_89 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 9.00/1.48  fof(f16462,plain,(
% 9.00/1.48    ( ! [X42] : (k4_xboole_0(X42,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X42,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X42,sK2),k4_xboole_0(X42,sK1)))) ) | (~spl3_149 | ~spl3_217)),
% 9.00/1.48    inference(superposition,[],[f14871,f6427])).
% 9.00/1.48  fof(f6427,plain,(
% 9.00/1.48    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2))) ) | ~spl3_149),
% 9.00/1.48    inference(avatar_component_clause,[],[f6426])).
% 9.00/1.48  fof(f6426,plain,(
% 9.00/1.48    spl3_149 <=> ! [X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).
% 9.00/1.48  fof(f14871,plain,(
% 9.00/1.48    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | ~spl3_217),
% 9.00/1.48    inference(avatar_component_clause,[],[f14870])).
% 9.00/1.48  fof(f14870,plain,(
% 9.00/1.48    spl3_217 <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_217])])).
% 9.00/1.48  fof(f19735,plain,(
% 9.00/1.48    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_43 | ~spl3_45 | spl3_69 | ~spl3_89 | ~spl3_90 | ~spl3_227)),
% 9.00/1.48    inference(backward_demodulation,[],[f979,f19733])).
% 9.00/1.48  fof(f19733,plain,(
% 9.00/1.48    ( ! [X28,X26,X27] : (k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,X28))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_43 | ~spl3_45 | ~spl3_89 | ~spl3_90 | ~spl3_227)),
% 9.00/1.48    inference(forward_demodulation,[],[f19732,f1710])).
% 9.00/1.48  fof(f1710,plain,(
% 9.00/1.48    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X30,X31)))))) ) | (~spl3_43 | ~spl3_45 | ~spl3_90)),
% 9.00/1.48    inference(forward_demodulation,[],[f1709,f592])).
% 9.00/1.48  fof(f1709,plain,(
% 9.00/1.48    ( ! [X30,X31,X29] : (k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,X31)))) ) | (~spl3_43 | ~spl3_45 | ~spl3_90)),
% 9.00/1.48    inference(forward_demodulation,[],[f1708,f560])).
% 9.00/1.48  fof(f560,plain,(
% 9.00/1.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | ~spl3_43),
% 9.00/1.48    inference(avatar_component_clause,[],[f559])).
% 9.00/1.48  fof(f559,plain,(
% 9.00/1.48    spl3_43 <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 9.00/1.48  fof(f1708,plain,(
% 9.00/1.48    ( ! [X30,X31,X29] : (k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k1_xboole_0),X31)))) ) | (~spl3_45 | ~spl3_90)),
% 9.00/1.48    inference(forward_demodulation,[],[f1707,f592])).
% 9.00/1.48  fof(f1707,plain,(
% 9.00/1.48    ( ! [X30,X31,X29] : (k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X30,k1_xboole_0))),X31)) ) | (~spl3_45 | ~spl3_90)),
% 9.00/1.48    inference(forward_demodulation,[],[f1668,f592])).
% 9.00/1.48  fof(f1668,plain,(
% 9.00/1.48    ( ! [X30,X31,X29] : (k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k4_xboole_0(X30,X31))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X29,k4_xboole_0(X29,X30)),k1_xboole_0),X31)) ) | (~spl3_45 | ~spl3_90)),
% 9.00/1.48    inference(superposition,[],[f592,f1617])).
% 9.00/1.48  fof(f1617,plain,(
% 9.00/1.48    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)) ) | ~spl3_90),
% 9.00/1.48    inference(avatar_component_clause,[],[f1616])).
% 9.00/1.48  fof(f1616,plain,(
% 9.00/1.48    spl3_90 <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 9.00/1.48  fof(f19732,plain,(
% 9.00/1.48    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,X27))))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30 | ~spl3_89 | ~spl3_227)),
% 9.00/1.48    inference(forward_demodulation,[],[f18974,f430])).
% 9.00/1.48  fof(f430,plain,(
% 9.00/1.48    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | (~spl3_11 | ~spl3_19 | ~spl3_30)),
% 9.00/1.48    inference(forward_demodulation,[],[f388,f188])).
% 9.00/1.48  fof(f388,plain,(
% 9.00/1.48    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | (~spl3_11 | ~spl3_30)),
% 9.00/1.48    inference(superposition,[],[f328,f109])).
% 9.00/1.48  fof(f18974,plain,(
% 9.00/1.48    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X27)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X26,X27))))))) ) | (~spl3_89 | ~spl3_227)),
% 9.00/1.48    inference(superposition,[],[f14911,f1613])).
% 9.00/1.48  fof(f14911,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12))))) ) | ~spl3_227),
% 9.00/1.48    inference(avatar_component_clause,[],[f14910])).
% 9.00/1.48  fof(f14910,plain,(
% 9.00/1.48    spl3_227 <=> ! [X11,X10,X12] : k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12))))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_227])])).
% 9.00/1.48  fof(f979,plain,(
% 9.00/1.48    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) | spl3_69),
% 9.00/1.48    inference(avatar_component_clause,[],[f977])).
% 9.00/1.48  fof(f977,plain,(
% 9.00/1.48    spl3_69 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 9.00/1.48  fof(f14912,plain,(
% 9.00/1.48    spl3_227 | ~spl3_29 | ~spl3_30 | ~spl3_45 | ~spl3_164 | ~spl3_202),
% 9.00/1.48    inference(avatar_split_clause,[],[f14046,f11335,f7946,f591,f327,f323,f14910])).
% 9.00/1.48  fof(f323,plain,(
% 9.00/1.48    spl3_29 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 9.00/1.48  fof(f7946,plain,(
% 9.00/1.48    spl3_164 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).
% 9.00/1.48  fof(f14046,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X12))))) ) | (~spl3_29 | ~spl3_30 | ~spl3_45 | ~spl3_164 | ~spl3_202)),
% 9.00/1.48    inference(backward_demodulation,[],[f821,f14043])).
% 9.00/1.48  fof(f14043,plain,(
% 9.00/1.48    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(X214,X215)) = k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))) ) | (~spl3_29 | ~spl3_45 | ~spl3_164 | ~spl3_202)),
% 9.00/1.48    inference(forward_demodulation,[],[f14042,f13978])).
% 9.00/1.48  fof(f13978,plain,(
% 9.00/1.48    ( ! [X30,X31,X32] : (k4_xboole_0(X30,k4_xboole_0(X31,X32)) = k5_xboole_0(X30,k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X30,X32))))) ) | (~spl3_29 | ~spl3_45 | ~spl3_202)),
% 9.00/1.48    inference(forward_demodulation,[],[f13309,f592])).
% 9.00/1.48  fof(f13309,plain,(
% 9.00/1.48    ( ! [X30,X31,X32] : (k4_xboole_0(X30,k4_xboole_0(X31,X32)) = k5_xboole_0(X30,k4_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,X30)),X32))) ) | (~spl3_29 | ~spl3_202)),
% 9.00/1.48    inference(superposition,[],[f324,f11336])).
% 9.00/1.48  fof(f324,plain,(
% 9.00/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_29),
% 9.00/1.48    inference(avatar_component_clause,[],[f323])).
% 9.00/1.48  fof(f14042,plain,(
% 9.00/1.48    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215)))) = k5_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))) ) | (~spl3_45 | ~spl3_164 | ~spl3_202)),
% 9.00/1.48    inference(forward_demodulation,[],[f13357,f592])).
% 9.00/1.48  fof(f13357,plain,(
% 9.00/1.48    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215)) = k5_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215))) ) | (~spl3_164 | ~spl3_202)),
% 9.00/1.48    inference(superposition,[],[f7947,f11336])).
% 9.00/1.48  fof(f7947,plain,(
% 9.00/1.48    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl3_164),
% 9.00/1.48    inference(avatar_component_clause,[],[f7946])).
% 9.00/1.48  fof(f821,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))))))) ) | (~spl3_30 | ~spl3_45)),
% 9.00/1.48    inference(forward_demodulation,[],[f761,f592])).
% 9.00/1.48  fof(f761,plain,(
% 9.00/1.48    ( ! [X12,X10,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X12))))) ) | (~spl3_30 | ~spl3_45)),
% 9.00/1.48    inference(superposition,[],[f592,f328])).
% 9.00/1.48  fof(f14872,plain,(
% 9.00/1.48    spl3_217 | ~spl3_74 | ~spl3_134),
% 9.00/1.48    inference(avatar_split_clause,[],[f5443,f4372,f1191,f14870])).
% 9.00/1.48  fof(f1191,plain,(
% 9.00/1.48    spl3_74 <=> ! [X5,X4] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 9.00/1.48  fof(f4372,plain,(
% 9.00/1.48    spl3_134 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 9.00/1.48    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).
% 9.00/1.48  fof(f5443,plain,(
% 9.00/1.48    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | (~spl3_74 | ~spl3_134)),
% 9.00/1.48    inference(superposition,[],[f1192,f4373])).
% 9.00/1.49  fof(f4373,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl3_134),
% 9.00/1.49    inference(avatar_component_clause,[],[f4372])).
% 9.00/1.49  fof(f1192,plain,(
% 9.00/1.49    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) ) | ~spl3_74),
% 9.00/1.49    inference(avatar_component_clause,[],[f1191])).
% 9.00/1.49  fof(f11337,plain,(
% 9.00/1.49    spl3_202 | ~spl3_30 | ~spl3_45),
% 9.00/1.49    inference(avatar_split_clause,[],[f751,f591,f327,f11335])).
% 9.00/1.49  fof(f751,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | (~spl3_30 | ~spl3_45)),
% 9.00/1.49    inference(superposition,[],[f592,f328])).
% 9.00/1.49  fof(f7948,plain,(
% 9.00/1.49    spl3_164 | ~spl3_2 | ~spl3_29 | ~spl3_44 | ~spl3_65),
% 9.00/1.49    inference(avatar_split_clause,[],[f1111,f961,f563,f323,f54,f7946])).
% 9.00/1.49  fof(f54,plain,(
% 9.00/1.49    spl3_2 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 9.00/1.49  fof(f563,plain,(
% 9.00/1.49    spl3_44 <=> ! [X15] : k1_xboole_0 = k5_xboole_0(X15,X15)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 9.00/1.49  fof(f961,plain,(
% 9.00/1.49    spl3_65 <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 9.00/1.49  fof(f1111,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl3_2 | ~spl3_29 | ~spl3_44 | ~spl3_65)),
% 9.00/1.49    inference(forward_demodulation,[],[f1073,f1100])).
% 9.00/1.49  fof(f1100,plain,(
% 9.00/1.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_2 | ~spl3_44 | ~spl3_65)),
% 9.00/1.49    inference(forward_demodulation,[],[f1072,f55])).
% 9.00/1.49  fof(f55,plain,(
% 9.00/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 9.00/1.49    inference(avatar_component_clause,[],[f54])).
% 9.00/1.49  fof(f1072,plain,(
% 9.00/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl3_44 | ~spl3_65)),
% 9.00/1.49    inference(superposition,[],[f962,f564])).
% 9.00/1.49  fof(f564,plain,(
% 9.00/1.49    ( ! [X15] : (k1_xboole_0 = k5_xboole_0(X15,X15)) ) | ~spl3_44),
% 9.00/1.49    inference(avatar_component_clause,[],[f563])).
% 9.00/1.49  fof(f962,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | ~spl3_65),
% 9.00/1.49    inference(avatar_component_clause,[],[f961])).
% 9.00/1.49  fof(f1073,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl3_29 | ~spl3_65)),
% 9.00/1.49    inference(superposition,[],[f962,f324])).
% 9.00/1.49  fof(f6428,plain,(
% 9.00/1.49    spl3_149 | ~spl3_12 | ~spl3_19 | ~spl3_27 | ~spl3_148),
% 9.00/1.49    inference(avatar_split_clause,[],[f6392,f6352,f295,f187,f119,f6426])).
% 9.00/1.49  fof(f119,plain,(
% 9.00/1.49    spl3_12 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 9.00/1.49  fof(f295,plain,(
% 9.00/1.49    spl3_27 <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 9.00/1.49  fof(f6352,plain,(
% 9.00/1.49    spl3_148 <=> ! [X46] : r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).
% 9.00/1.49  fof(f6392,plain,(
% 9.00/1.49    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2))) ) | (~spl3_12 | ~spl3_19 | ~spl3_27 | ~spl3_148)),
% 9.00/1.49    inference(forward_demodulation,[],[f6391,f296])).
% 9.00/1.49  fof(f296,plain,(
% 9.00/1.49    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) ) | ~spl3_27),
% 9.00/1.49    inference(avatar_component_clause,[],[f295])).
% 9.00/1.49  fof(f6391,plain,(
% 9.00/1.49    ( ! [X9] : (k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)))) ) | (~spl3_12 | ~spl3_19 | ~spl3_148)),
% 9.00/1.49    inference(forward_demodulation,[],[f6361,f188])).
% 9.00/1.49  fof(f6361,plain,(
% 9.00/1.49    ( ! [X9] : (k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,sK1),k4_xboole_0(X9,sK2)),k1_xboole_0))) ) | (~spl3_12 | ~spl3_148)),
% 9.00/1.49    inference(resolution,[],[f6353,f120])).
% 9.00/1.49  fof(f120,plain,(
% 9.00/1.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_12),
% 9.00/1.49    inference(avatar_component_clause,[],[f119])).
% 9.00/1.49  fof(f6353,plain,(
% 9.00/1.49    ( ! [X46] : (r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0)) ) | ~spl3_148),
% 9.00/1.49    inference(avatar_component_clause,[],[f6352])).
% 9.00/1.49  fof(f6354,plain,(
% 9.00/1.49    spl3_148 | ~spl3_11 | ~spl3_18 | ~spl3_19 | ~spl3_45 | ~spl3_84 | ~spl3_89 | ~spl3_146),
% 9.00/1.49    inference(avatar_split_clause,[],[f6334,f6081,f1612,f1541,f591,f187,f176,f108,f6352])).
% 9.00/1.49  fof(f176,plain,(
% 9.00/1.49    spl3_18 <=> k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 9.00/1.49  fof(f1541,plain,(
% 9.00/1.49    spl3_84 <=> ! [X8] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 9.00/1.49  fof(f6081,plain,(
% 9.00/1.49    spl3_146 <=> ! [X53,X52] : r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52)))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).
% 9.00/1.49  fof(f6334,plain,(
% 9.00/1.49    ( ! [X46] : (r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,sK2)),k1_xboole_0)) ) | (~spl3_11 | ~spl3_18 | ~spl3_19 | ~spl3_45 | ~spl3_84 | ~spl3_89 | ~spl3_146)),
% 9.00/1.49    inference(forward_demodulation,[],[f6333,f2253])).
% 9.00/1.49  fof(f6333,plain,(
% 9.00/1.49    ( ! [X46] : (r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(k4_xboole_0(X46,sK1),sK2)),k1_xboole_0)) ) | (~spl3_18 | ~spl3_84 | ~spl3_146)),
% 9.00/1.49    inference(forward_demodulation,[],[f6179,f178])).
% 9.00/1.49  fof(f178,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl3_18),
% 9.00/1.49    inference(avatar_component_clause,[],[f176])).
% 9.00/1.49  fof(f6179,plain,(
% 9.00/1.49    ( ! [X46] : (r1_tarski(k4_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(k4_xboole_0(X46,sK1),sK2)),k4_xboole_0(sK2,sK2))) ) | (~spl3_84 | ~spl3_146)),
% 9.00/1.49    inference(superposition,[],[f6082,f1542])).
% 9.00/1.49  fof(f1542,plain,(
% 9.00/1.49    ( ! [X8] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))) ) | ~spl3_84),
% 9.00/1.49    inference(avatar_component_clause,[],[f1541])).
% 9.00/1.49  fof(f6082,plain,(
% 9.00/1.49    ( ! [X52,X53] : (r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52)))) ) | ~spl3_146),
% 9.00/1.49    inference(avatar_component_clause,[],[f6081])).
% 9.00/1.49  fof(f6083,plain,(
% 9.00/1.49    spl3_146 | ~spl3_61 | ~spl3_145),
% 9.00/1.49    inference(avatar_split_clause,[],[f5898,f5812,f862,f6081])).
% 9.00/1.49  fof(f862,plain,(
% 9.00/1.49    spl3_61 <=> ! [X5,X6] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 9.00/1.49  fof(f5812,plain,(
% 9.00/1.49    spl3_145 <=> ! [X16,X17] : k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).
% 9.00/1.49  fof(f5898,plain,(
% 9.00/1.49    ( ! [X52,X53] : (r1_tarski(k4_xboole_0(X52,k4_xboole_0(X52,X53)),k4_xboole_0(X53,k4_xboole_0(X53,X52)))) ) | (~spl3_61 | ~spl3_145)),
% 9.00/1.49    inference(superposition,[],[f863,f5813])).
% 9.00/1.49  fof(f5813,plain,(
% 9.00/1.49    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16)) ) | ~spl3_145),
% 9.00/1.49    inference(avatar_component_clause,[],[f5812])).
% 9.00/1.49  fof(f863,plain,(
% 9.00/1.49    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) ) | ~spl3_61),
% 9.00/1.49    inference(avatar_component_clause,[],[f862])).
% 9.00/1.49  fof(f5814,plain,(
% 9.00/1.49    spl3_145 | ~spl3_43 | ~spl3_45 | ~spl3_90 | ~spl3_134),
% 9.00/1.49    inference(avatar_split_clause,[],[f5467,f4372,f1616,f591,f559,f5812])).
% 9.00/1.49  fof(f5467,plain,(
% 9.00/1.49    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k4_xboole_0(X17,X16)) ) | (~spl3_43 | ~spl3_45 | ~spl3_90 | ~spl3_134)),
% 9.00/1.49    inference(forward_demodulation,[],[f5466,f4373])).
% 9.00/1.49  fof(f5466,plain,(
% 9.00/1.49    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) ) | (~spl3_43 | ~spl3_45 | ~spl3_90 | ~spl3_134)),
% 9.00/1.49    inference(forward_demodulation,[],[f5465,f560])).
% 9.00/1.49  fof(f5465,plain,(
% 9.00/1.49    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k1_xboole_0))))) ) | (~spl3_45 | ~spl3_90 | ~spl3_134)),
% 9.00/1.49    inference(forward_demodulation,[],[f5399,f592])).
% 9.00/1.49  fof(f5399,plain,(
% 9.00/1.49    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k1_xboole_0))) ) | (~spl3_90 | ~spl3_134)),
% 9.00/1.49    inference(superposition,[],[f4373,f1617])).
% 9.00/1.49  fof(f4374,plain,(
% 9.00/1.49    spl3_134 | ~spl3_29 | ~spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f402,f327,f323,f4372])).
% 9.00/1.49  fof(f402,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl3_29 | ~spl3_30)),
% 9.00/1.49    inference(superposition,[],[f324,f328])).
% 9.00/1.49  fof(f1618,plain,(
% 9.00/1.49    spl3_90 | ~spl3_11 | ~spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f406,f327,f108,f1616])).
% 9.00/1.49  fof(f406,plain,(
% 9.00/1.49    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)) ) | (~spl3_11 | ~spl3_30)),
% 9.00/1.49    inference(superposition,[],[f109,f328])).
% 9.00/1.49  fof(f1614,plain,(
% 9.00/1.49    spl3_89),
% 9.00/1.49    inference(avatar_split_clause,[],[f47,f1612])).
% 9.00/1.49  fof(f47,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 9.00/1.49    inference(forward_demodulation,[],[f44,f43])).
% 9.00/1.49  fof(f43,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 9.00/1.49    inference(definition_unfolding,[],[f35,f30,f30])).
% 9.00/1.49  fof(f30,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f9])).
% 9.00/1.49  fof(f9,axiom,(
% 9.00/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.00/1.49  fof(f35,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 9.00/1.49    inference(cnf_transformation,[],[f10])).
% 9.00/1.49  fof(f10,axiom,(
% 9.00/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 9.00/1.49  fof(f44,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 9.00/1.49    inference(definition_unfolding,[],[f36,f30,f30,f30,f30])).
% 9.00/1.49  fof(f36,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f4])).
% 9.00/1.49  fof(f4,axiom,(
% 9.00/1.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 9.00/1.49  fof(f1543,plain,(
% 9.00/1.49    spl3_84 | ~spl3_2 | ~spl3_29 | ~spl3_83),
% 9.00/1.49    inference(avatar_split_clause,[],[f1532,f1436,f323,f54,f1541])).
% 9.00/1.49  fof(f1436,plain,(
% 9.00/1.49    spl3_83 <=> ! [X9] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 9.00/1.49  fof(f1532,plain,(
% 9.00/1.49    ( ! [X8] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))) ) | (~spl3_2 | ~spl3_29 | ~spl3_83)),
% 9.00/1.49    inference(forward_demodulation,[],[f1507,f55])).
% 9.00/1.49  fof(f1507,plain,(
% 9.00/1.49    ( ! [X8] : (k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X8,sK1))) ) | (~spl3_29 | ~spl3_83)),
% 9.00/1.49    inference(superposition,[],[f324,f1437])).
% 9.00/1.49  fof(f1437,plain,(
% 9.00/1.49    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))) ) | ~spl3_83),
% 9.00/1.49    inference(avatar_component_clause,[],[f1436])).
% 9.00/1.49  fof(f1438,plain,(
% 9.00/1.49    spl3_83 | ~spl3_45 | ~spl3_51),
% 9.00/1.49    inference(avatar_split_clause,[],[f760,f639,f591,f1436])).
% 9.00/1.49  fof(f639,plain,(
% 9.00/1.49    spl3_51 <=> ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 9.00/1.49  fof(f760,plain,(
% 9.00/1.49    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X9,sK1)))) ) | (~spl3_45 | ~spl3_51)),
% 9.00/1.49    inference(superposition,[],[f592,f640])).
% 9.00/1.49  fof(f640,plain,(
% 9.00/1.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1)) ) | ~spl3_51),
% 9.00/1.49    inference(avatar_component_clause,[],[f639])).
% 9.00/1.49  fof(f1193,plain,(
% 9.00/1.49    spl3_74 | ~spl3_2 | ~spl3_64 | ~spl3_73),
% 9.00/1.49    inference(avatar_split_clause,[],[f1181,f1157,f957,f54,f1191])).
% 9.00/1.49  fof(f957,plain,(
% 9.00/1.49    spl3_64 <=> ! [X3,X2] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 9.00/1.49  fof(f1157,plain,(
% 9.00/1.49    spl3_73 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 9.00/1.49  fof(f1181,plain,(
% 9.00/1.49    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) ) | (~spl3_2 | ~spl3_64 | ~spl3_73)),
% 9.00/1.49    inference(forward_demodulation,[],[f1163,f55])).
% 9.00/1.49  fof(f1163,plain,(
% 9.00/1.49    ( ! [X4,X5] : (k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5))) ) | (~spl3_64 | ~spl3_73)),
% 9.00/1.49    inference(superposition,[],[f1158,f958])).
% 9.00/1.49  fof(f958,plain,(
% 9.00/1.49    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) ) | ~spl3_64),
% 9.00/1.49    inference(avatar_component_clause,[],[f957])).
% 9.00/1.49  fof(f1158,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | ~spl3_73),
% 9.00/1.49    inference(avatar_component_clause,[],[f1157])).
% 9.00/1.49  fof(f1159,plain,(
% 9.00/1.49    spl3_73 | ~spl3_2 | ~spl3_28 | ~spl3_44 | ~spl3_53 | ~spl3_65),
% 9.00/1.49    inference(avatar_split_clause,[],[f1109,f961,f647,f563,f319,f54,f1157])).
% 9.00/1.49  fof(f319,plain,(
% 9.00/1.49    spl3_28 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 9.00/1.49  fof(f647,plain,(
% 9.00/1.49    spl3_53 <=> ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 9.00/1.49  fof(f1109,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | (~spl3_2 | ~spl3_28 | ~spl3_44 | ~spl3_53 | ~spl3_65)),
% 9.00/1.49    inference(forward_demodulation,[],[f1103,f1100])).
% 9.00/1.49  fof(f1103,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) ) | (~spl3_2 | ~spl3_28 | ~spl3_44 | ~spl3_53 | ~spl3_65)),
% 9.00/1.49    inference(backward_demodulation,[],[f701,f1100])).
% 9.00/1.49  fof(f701,plain,(
% 9.00/1.49    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) ) | (~spl3_28 | ~spl3_53)),
% 9.00/1.49    inference(superposition,[],[f320,f648])).
% 9.00/1.49  fof(f648,plain,(
% 9.00/1.49    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) ) | ~spl3_53),
% 9.00/1.49    inference(avatar_component_clause,[],[f647])).
% 9.00/1.49  fof(f320,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl3_28),
% 9.00/1.49    inference(avatar_component_clause,[],[f319])).
% 9.00/1.49  fof(f980,plain,(
% 9.00/1.49    ~spl3_69),
% 9.00/1.49    inference(avatar_split_clause,[],[f46,f977])).
% 9.00/1.49  fof(f46,plain,(
% 9.00/1.49    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 9.00/1.49    inference(backward_demodulation,[],[f39,f43])).
% 9.00/1.49  fof(f39,plain,(
% 9.00/1.49    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 9.00/1.49    inference(definition_unfolding,[],[f23,f28,f30])).
% 9.00/1.49  fof(f28,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f13])).
% 9.00/1.49  fof(f13,axiom,(
% 9.00/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 9.00/1.49  fof(f23,plain,(
% 9.00/1.49    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 9.00/1.49    inference(cnf_transformation,[],[f20])).
% 9.00/1.49  fof(f20,plain,(
% 9.00/1.49    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 9.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 9.00/1.49  fof(f19,plain,(
% 9.00/1.49    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 9.00/1.49    introduced(choice_axiom,[])).
% 9.00/1.49  fof(f16,plain,(
% 9.00/1.49    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 9.00/1.49    inference(ennf_transformation,[],[f15])).
% 9.00/1.49  fof(f15,negated_conjecture,(
% 9.00/1.49    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 9.00/1.49    inference(negated_conjecture,[],[f14])).
% 9.00/1.49  fof(f14,conjecture,(
% 9.00/1.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 9.00/1.49  fof(f963,plain,(
% 9.00/1.49    spl3_65 | ~spl3_28 | ~spl3_44),
% 9.00/1.49    inference(avatar_split_clause,[],[f587,f563,f319,f961])).
% 9.00/1.49  fof(f587,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl3_28 | ~spl3_44)),
% 9.00/1.49    inference(superposition,[],[f320,f564])).
% 9.00/1.49  fof(f959,plain,(
% 9.00/1.49    spl3_64 | ~spl3_28 | ~spl3_44),
% 9.00/1.49    inference(avatar_split_clause,[],[f586,f563,f319,f957])).
% 9.00/1.49  fof(f586,plain,(
% 9.00/1.49    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) ) | (~spl3_28 | ~spl3_44)),
% 9.00/1.49    inference(superposition,[],[f564,f320])).
% 9.00/1.49  fof(f864,plain,(
% 9.00/1.49    spl3_61 | ~spl3_3 | ~spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f404,f327,f58,f862])).
% 9.00/1.49  fof(f58,plain,(
% 9.00/1.49    spl3_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 9.00/1.49  fof(f404,plain,(
% 9.00/1.49    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) ) | (~spl3_3 | ~spl3_30)),
% 9.00/1.49    inference(superposition,[],[f59,f328])).
% 9.00/1.49  fof(f59,plain,(
% 9.00/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 9.00/1.49    inference(avatar_component_clause,[],[f58])).
% 9.00/1.49  fof(f649,plain,(
% 9.00/1.49    spl3_53 | ~spl3_31 | ~spl3_44),
% 9.00/1.49    inference(avatar_split_clause,[],[f585,f563,f337,f647])).
% 9.00/1.49  fof(f337,plain,(
% 9.00/1.49    spl3_31 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 9.00/1.49  fof(f585,plain,(
% 9.00/1.49    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) ) | (~spl3_31 | ~spl3_44)),
% 9.00/1.49    inference(superposition,[],[f564,f338])).
% 9.00/1.49  fof(f338,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) ) | ~spl3_31),
% 9.00/1.49    inference(avatar_component_clause,[],[f337])).
% 9.00/1.49  fof(f641,plain,(
% 9.00/1.49    spl3_51 | ~spl3_5 | ~spl3_36),
% 9.00/1.49    inference(avatar_split_clause,[],[f472,f468,f66,f639])).
% 9.00/1.49  fof(f66,plain,(
% 9.00/1.49    spl3_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 9.00/1.49  fof(f468,plain,(
% 9.00/1.49    spl3_36 <=> ! [X1] : r1_tarski(k4_xboole_0(sK2,X1),sK1)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 9.00/1.49  fof(f472,plain,(
% 9.00/1.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X1),sK1)) ) | (~spl3_5 | ~spl3_36)),
% 9.00/1.49    inference(resolution,[],[f469,f67])).
% 9.00/1.49  fof(f67,plain,(
% 9.00/1.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_5),
% 9.00/1.49    inference(avatar_component_clause,[],[f66])).
% 9.00/1.49  fof(f469,plain,(
% 9.00/1.49    ( ! [X1] : (r1_tarski(k4_xboole_0(sK2,X1),sK1)) ) | ~spl3_36),
% 9.00/1.49    inference(avatar_component_clause,[],[f468])).
% 9.00/1.49  fof(f593,plain,(
% 9.00/1.49    spl3_45),
% 9.00/1.49    inference(avatar_split_clause,[],[f43,f591])).
% 9.00/1.49  fof(f565,plain,(
% 9.00/1.49    spl3_44 | ~spl3_2 | ~spl3_29 | ~spl3_38),
% 9.00/1.49    inference(avatar_split_clause,[],[f527,f486,f323,f54,f563])).
% 9.00/1.49  fof(f486,plain,(
% 9.00/1.49    spl3_38 <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 9.00/1.49  fof(f527,plain,(
% 9.00/1.49    ( ! [X15] : (k1_xboole_0 = k5_xboole_0(X15,X15)) ) | (~spl3_2 | ~spl3_29 | ~spl3_38)),
% 9.00/1.49    inference(forward_demodulation,[],[f519,f522])).
% 9.00/1.49  fof(f522,plain,(
% 9.00/1.49    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl3_2 | ~spl3_29 | ~spl3_38)),
% 9.00/1.49    inference(forward_demodulation,[],[f508,f55])).
% 9.00/1.49  fof(f508,plain,(
% 9.00/1.49    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) ) | (~spl3_29 | ~spl3_38)),
% 9.00/1.49    inference(superposition,[],[f324,f487])).
% 9.00/1.49  fof(f487,plain,(
% 9.00/1.49    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))) ) | ~spl3_38),
% 9.00/1.49    inference(avatar_component_clause,[],[f486])).
% 9.00/1.49  fof(f519,plain,(
% 9.00/1.49    ( ! [X15] : (k1_xboole_0 = k5_xboole_0(X15,k4_xboole_0(X15,k1_xboole_0))) ) | (~spl3_29 | ~spl3_38)),
% 9.00/1.49    inference(superposition,[],[f324,f487])).
% 9.00/1.49  fof(f561,plain,(
% 9.00/1.49    spl3_43 | ~spl3_2 | ~spl3_29 | ~spl3_38),
% 9.00/1.49    inference(avatar_split_clause,[],[f522,f486,f323,f54,f559])).
% 9.00/1.49  fof(f488,plain,(
% 9.00/1.49    spl3_38 | ~spl3_10 | ~spl3_20 | ~spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f432,f327,f207,f100,f486])).
% 9.00/1.49  fof(f100,plain,(
% 9.00/1.49    spl3_10 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 9.00/1.49  fof(f207,plain,(
% 9.00/1.49    spl3_20 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 9.00/1.49  fof(f432,plain,(
% 9.00/1.49    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))) ) | (~spl3_10 | ~spl3_20 | ~spl3_30)),
% 9.00/1.49    inference(forward_demodulation,[],[f390,f102])).
% 9.00/1.49  fof(f102,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_10),
% 9.00/1.49    inference(avatar_component_clause,[],[f100])).
% 9.00/1.49  fof(f390,plain,(
% 9.00/1.49    ( ! [X10] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X10,k1_xboole_0))) ) | (~spl3_20 | ~spl3_30)),
% 9.00/1.49    inference(superposition,[],[f328,f208])).
% 9.00/1.49  fof(f208,plain,(
% 9.00/1.49    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) ) | ~spl3_20),
% 9.00/1.49    inference(avatar_component_clause,[],[f207])).
% 9.00/1.49  fof(f470,plain,(
% 9.00/1.49    spl3_36 | ~spl3_3 | ~spl3_35),
% 9.00/1.49    inference(avatar_split_clause,[],[f463,f459,f58,f468])).
% 9.00/1.49  fof(f459,plain,(
% 9.00/1.49    spl3_35 <=> ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK1))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 9.00/1.49  fof(f463,plain,(
% 9.00/1.49    ( ! [X1] : (r1_tarski(k4_xboole_0(sK2,X1),sK1)) ) | (~spl3_3 | ~spl3_35)),
% 9.00/1.49    inference(resolution,[],[f460,f59])).
% 9.00/1.49  fof(f460,plain,(
% 9.00/1.49    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK1)) ) | ~spl3_35),
% 9.00/1.49    inference(avatar_component_clause,[],[f459])).
% 9.00/1.49  fof(f461,plain,(
% 9.00/1.49    spl3_35 | ~spl3_15 | ~spl3_34),
% 9.00/1.49    inference(avatar_split_clause,[],[f446,f441,f146,f459])).
% 9.00/1.49  fof(f146,plain,(
% 9.00/1.49    spl3_15 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 9.00/1.49  fof(f441,plain,(
% 9.00/1.49    spl3_34 <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 9.00/1.49  fof(f446,plain,(
% 9.00/1.49    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK1)) ) | (~spl3_15 | ~spl3_34)),
% 9.00/1.49    inference(superposition,[],[f147,f443])).
% 9.00/1.49  fof(f443,plain,(
% 9.00/1.49    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_34),
% 9.00/1.49    inference(avatar_component_clause,[],[f441])).
% 9.00/1.49  fof(f147,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r1_tarski(X0,X1)) ) | ~spl3_15),
% 9.00/1.49    inference(avatar_component_clause,[],[f146])).
% 9.00/1.49  fof(f444,plain,(
% 9.00/1.49    spl3_34 | ~spl3_6 | ~spl3_16 | ~spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f433,f327,f157,f72,f441])).
% 9.00/1.49  fof(f72,plain,(
% 9.00/1.49    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 9.00/1.49  fof(f157,plain,(
% 9.00/1.49    spl3_16 <=> sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 9.00/1.49  fof(f433,plain,(
% 9.00/1.49    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_6 | ~spl3_16 | ~spl3_30)),
% 9.00/1.49    inference(forward_demodulation,[],[f391,f159])).
% 9.00/1.49  fof(f159,plain,(
% 9.00/1.49    sK2 = k4_xboole_0(sK2,k1_xboole_0) | ~spl3_16),
% 9.00/1.49    inference(avatar_component_clause,[],[f157])).
% 9.00/1.49  fof(f391,plain,(
% 9.00/1.49    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) | (~spl3_6 | ~spl3_30)),
% 9.00/1.49    inference(superposition,[],[f328,f74])).
% 9.00/1.49  fof(f74,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_6),
% 9.00/1.49    inference(avatar_component_clause,[],[f72])).
% 9.00/1.49  fof(f339,plain,(
% 9.00/1.49    spl3_31 | ~spl3_2 | ~spl3_28),
% 9.00/1.49    inference(avatar_split_clause,[],[f330,f319,f54,f337])).
% 9.00/1.49  fof(f330,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) ) | (~spl3_2 | ~spl3_28)),
% 9.00/1.49    inference(superposition,[],[f320,f55])).
% 9.00/1.49  fof(f329,plain,(
% 9.00/1.49    spl3_30),
% 9.00/1.49    inference(avatar_split_clause,[],[f41,f327])).
% 9.00/1.49  fof(f41,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 9.00/1.49    inference(definition_unfolding,[],[f27,f30,f30])).
% 9.00/1.49  fof(f27,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.00/1.49    inference(cnf_transformation,[],[f1])).
% 9.00/1.49  fof(f1,axiom,(
% 9.00/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.00/1.49  fof(f325,plain,(
% 9.00/1.49    spl3_29),
% 9.00/1.49    inference(avatar_split_clause,[],[f38,f323])).
% 9.00/1.49  fof(f38,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 9.00/1.49    inference(definition_unfolding,[],[f29,f30])).
% 9.00/1.49  fof(f29,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f3])).
% 9.00/1.49  fof(f3,axiom,(
% 9.00/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.00/1.49  fof(f321,plain,(
% 9.00/1.49    spl3_28),
% 9.00/1.49    inference(avatar_split_clause,[],[f34,f319])).
% 9.00/1.49  fof(f34,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f12])).
% 9.00/1.49  fof(f12,axiom,(
% 9.00/1.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 9.00/1.49  fof(f297,plain,(
% 9.00/1.49    spl3_27 | ~spl3_11 | ~spl3_19),
% 9.00/1.49    inference(avatar_split_clause,[],[f202,f187,f108,f295])).
% 9.00/1.49  fof(f202,plain,(
% 9.00/1.49    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) ) | (~spl3_11 | ~spl3_19)),
% 9.00/1.49    inference(superposition,[],[f109,f188])).
% 9.00/1.49  fof(f209,plain,(
% 9.00/1.49    spl3_20 | ~spl3_11 | ~spl3_19),
% 9.00/1.49    inference(avatar_split_clause,[],[f198,f187,f108,f207])).
% 9.00/1.49  fof(f198,plain,(
% 9.00/1.49    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) ) | (~spl3_11 | ~spl3_19)),
% 9.00/1.49    inference(superposition,[],[f188,f109])).
% 9.00/1.49  fof(f189,plain,(
% 9.00/1.49    spl3_19 | ~spl3_3 | ~spl3_11 | ~spl3_12),
% 9.00/1.49    inference(avatar_split_clause,[],[f155,f119,f108,f58,f187])).
% 9.00/1.49  fof(f155,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_11 | ~spl3_12)),
% 9.00/1.49    inference(forward_demodulation,[],[f150,f109])).
% 9.00/1.49  fof(f150,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ) | (~spl3_3 | ~spl3_12)),
% 9.00/1.49    inference(resolution,[],[f120,f59])).
% 9.00/1.49  fof(f179,plain,(
% 9.00/1.49    spl3_18 | ~spl3_11 | ~spl3_16),
% 9.00/1.49    inference(avatar_split_clause,[],[f163,f157,f108,f176])).
% 9.00/1.49  fof(f163,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(sK2,sK2) | (~spl3_11 | ~spl3_16)),
% 9.00/1.49    inference(superposition,[],[f109,f159])).
% 9.00/1.49  fof(f160,plain,(
% 9.00/1.49    spl3_16 | ~spl3_1 | ~spl3_6 | ~spl3_12),
% 9.00/1.49    inference(avatar_split_clause,[],[f154,f119,f72,f49,f157])).
% 9.00/1.49  fof(f49,plain,(
% 9.00/1.49    spl3_1 <=> r1_tarski(sK2,sK1)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 9.00/1.49  fof(f154,plain,(
% 9.00/1.49    sK2 = k4_xboole_0(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_6 | ~spl3_12)),
% 9.00/1.49    inference(forward_demodulation,[],[f149,f74])).
% 9.00/1.49  fof(f149,plain,(
% 9.00/1.49    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl3_1 | ~spl3_12)),
% 9.00/1.49    inference(resolution,[],[f120,f51])).
% 9.00/1.49  fof(f51,plain,(
% 9.00/1.49    r1_tarski(sK2,sK1) | ~spl3_1),
% 9.00/1.49    inference(avatar_component_clause,[],[f49])).
% 9.00/1.49  fof(f148,plain,(
% 9.00/1.49    spl3_15),
% 9.00/1.49    inference(avatar_split_clause,[],[f45,f146])).
% 9.00/1.49  fof(f45,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 9.00/1.49    inference(definition_unfolding,[],[f37,f30])).
% 9.00/1.49  fof(f37,plain,(
% 9.00/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 9.00/1.49    inference(cnf_transformation,[],[f18])).
% 9.00/1.49  fof(f18,plain,(
% 9.00/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 9.00/1.49    inference(ennf_transformation,[],[f6])).
% 9.00/1.49  fof(f6,axiom,(
% 9.00/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 9.00/1.49  fof(f121,plain,(
% 9.00/1.49    spl3_12),
% 9.00/1.49    inference(avatar_split_clause,[],[f42,f119])).
% 9.00/1.49  fof(f42,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 9.00/1.49    inference(definition_unfolding,[],[f31,f30])).
% 9.00/1.49  fof(f31,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 9.00/1.49    inference(cnf_transformation,[],[f17])).
% 9.00/1.49  fof(f17,plain,(
% 9.00/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 9.00/1.49    inference(ennf_transformation,[],[f7])).
% 9.00/1.49  fof(f7,axiom,(
% 9.00/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 9.00/1.49  fof(f110,plain,(
% 9.00/1.49    spl3_11 | ~spl3_3 | ~spl3_5),
% 9.00/1.49    inference(avatar_split_clause,[],[f70,f66,f58,f108])).
% 9.00/1.49  fof(f70,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_5)),
% 9.00/1.49    inference(resolution,[],[f67,f59])).
% 9.00/1.49  fof(f103,plain,(
% 9.00/1.49    spl3_10 | ~spl3_5 | ~spl3_9),
% 9.00/1.49    inference(avatar_split_clause,[],[f98,f94,f66,f100])).
% 9.00/1.49  fof(f94,plain,(
% 9.00/1.49    spl3_9 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 9.00/1.49  fof(f98,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_5 | ~spl3_9)),
% 9.00/1.49    inference(resolution,[],[f96,f67])).
% 9.00/1.49  fof(f96,plain,(
% 9.00/1.49    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_9),
% 9.00/1.49    inference(avatar_component_clause,[],[f94])).
% 9.00/1.49  fof(f97,plain,(
% 9.00/1.49    spl3_9 | ~spl3_3 | ~spl3_8),
% 9.00/1.49    inference(avatar_split_clause,[],[f91,f86,f58,f94])).
% 9.00/1.49  fof(f86,plain,(
% 9.00/1.49    spl3_8 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 9.00/1.49  fof(f91,plain,(
% 9.00/1.49    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_8)),
% 9.00/1.49    inference(superposition,[],[f59,f88])).
% 9.00/1.49  fof(f88,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_8),
% 9.00/1.49    inference(avatar_component_clause,[],[f86])).
% 9.00/1.49  fof(f89,plain,(
% 9.00/1.49    spl3_8 | ~spl3_5 | ~spl3_7),
% 9.00/1.49    inference(avatar_split_clause,[],[f84,f80,f66,f86])).
% 9.00/1.49  fof(f80,plain,(
% 9.00/1.49    spl3_7 <=> r1_tarski(k1_xboole_0,sK2)),
% 9.00/1.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 9.00/1.49  fof(f84,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | (~spl3_5 | ~spl3_7)),
% 9.00/1.49    inference(resolution,[],[f82,f67])).
% 9.00/1.49  fof(f82,plain,(
% 9.00/1.49    r1_tarski(k1_xboole_0,sK2) | ~spl3_7),
% 9.00/1.49    inference(avatar_component_clause,[],[f80])).
% 9.00/1.49  fof(f83,plain,(
% 9.00/1.49    spl3_7 | ~spl3_3 | ~spl3_6),
% 9.00/1.49    inference(avatar_split_clause,[],[f77,f72,f58,f80])).
% 9.00/1.49  fof(f77,plain,(
% 9.00/1.49    r1_tarski(k1_xboole_0,sK2) | (~spl3_3 | ~spl3_6)),
% 9.00/1.49    inference(superposition,[],[f59,f74])).
% 9.00/1.49  fof(f75,plain,(
% 9.00/1.49    spl3_6 | ~spl3_1 | ~spl3_5),
% 9.00/1.49    inference(avatar_split_clause,[],[f69,f66,f49,f72])).
% 9.00/1.49  fof(f69,plain,(
% 9.00/1.49    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_5)),
% 9.00/1.49    inference(resolution,[],[f67,f51])).
% 9.00/1.49  fof(f68,plain,(
% 9.00/1.49    spl3_5),
% 9.00/1.49    inference(avatar_split_clause,[],[f33,f66])).
% 9.00/1.49  fof(f33,plain,(
% 9.00/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 9.00/1.49    inference(cnf_transformation,[],[f21])).
% 9.00/1.49  fof(f21,plain,(
% 9.00/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 9.00/1.49    inference(nnf_transformation,[],[f2])).
% 9.00/1.49  fof(f2,axiom,(
% 9.00/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 9.00/1.49  fof(f60,plain,(
% 9.00/1.49    spl3_3),
% 9.00/1.49    inference(avatar_split_clause,[],[f25,f58])).
% 9.00/1.49  fof(f25,plain,(
% 9.00/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.00/1.49    inference(cnf_transformation,[],[f8])).
% 9.00/1.49  fof(f8,axiom,(
% 9.00/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 9.00/1.49  fof(f56,plain,(
% 9.00/1.49    spl3_2),
% 9.00/1.49    inference(avatar_split_clause,[],[f24,f54])).
% 9.00/1.49  fof(f24,plain,(
% 9.00/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.00/1.49    inference(cnf_transformation,[],[f11])).
% 9.00/1.49  fof(f11,axiom,(
% 9.00/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 9.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 9.00/1.49  fof(f52,plain,(
% 9.00/1.49    spl3_1),
% 9.00/1.49    inference(avatar_split_clause,[],[f22,f49])).
% 9.00/1.49  fof(f22,plain,(
% 9.00/1.49    r1_tarski(sK2,sK1)),
% 9.00/1.49    inference(cnf_transformation,[],[f20])).
% 9.00/1.49  % SZS output end Proof for theBenchmark
% 9.00/1.49  % (13949)------------------------------
% 9.00/1.49  % (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.00/1.49  % (13949)Termination reason: Refutation
% 9.00/1.49  
% 9.00/1.49  % (13949)Memory used [KB]: 29167
% 9.00/1.49  % (13949)Time elapsed: 0.946 s
% 9.00/1.49  % (13949)------------------------------
% 9.00/1.49  % (13949)------------------------------
% 9.00/1.49  % (13941)Success in time 1.129 s
%------------------------------------------------------------------------------
