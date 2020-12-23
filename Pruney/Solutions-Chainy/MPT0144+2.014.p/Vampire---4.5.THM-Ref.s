%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 262 expanded)
%              Number of leaves         :   15 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  173 ( 432 expanded)
%              Number of equality atoms :   76 ( 256 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10246)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f49,f70,f110,f168])).

fof(f168,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f37,f166])).

fof(f166,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X14)),X13)),X12)),X11))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f165,f89])).

fof(f89,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X7)),X6)),X5))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f88,f80])).

fof(f80,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f79,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_3
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X1),X2))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f78,f41])).

fof(f41,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl7_1
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f78,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f77,f69])).

fof(f77,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f71,f41])).

fof(f71,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0))
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(superposition,[],[f69,f41])).

fof(f88,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X5),X6),X7))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f87,f41])).

fof(f87,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X5),k5_xboole_0(X6,k4_xboole_0(X7,X6))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f86,f41])).

fof(f86,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f85,f80])).

fof(f85,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f84,f41])).

fof(f84,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),k5_xboole_0(X6,k4_xboole_0(X7,X6))),X4))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f72,f41])).

fof(f72,plain,
    ( ! [X6,X4,X8,X7,X5] : k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5))),X4))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f69,f48])).

fof(f48,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl7_2
  <=> ! [X1,X3,X0,X2] : k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f165,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),X12),X13),X14))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f164,f41])).

fof(f164,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),X12),k5_xboole_0(X13,k4_xboole_0(X14,X13))))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f163,f41])).

fof(f163,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12))))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f162,f41])).

fof(f162,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f161,f69])).

fof(f161,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),k4_xboole_0(k4_xboole_0(X15,X13),X14)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f160,f41])).

fof(f160,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),k4_xboole_0(X15,k5_xboole_0(X13,k4_xboole_0(X14,X13)))),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f159,f69])).

fof(f159,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),k4_xboole_0(k4_xboole_0(X15,X12),k5_xboole_0(X13,k4_xboole_0(X14,X13)))),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f158,f41])).

fof(f158,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),k4_xboole_0(X15,k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)))),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f157,f69])).

fof(f157,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(X15,X11),k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f124,f41])).

fof(f124,plain,
    ( ! [X14,X12,X10,X15,X13,X11] : k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(X15,k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f69,f109])).

fof(f109,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_4
  <=> ! [X1,X3,X0,X2,X4] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f37,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4))) ),
    inference(forward_demodulation,[],[f36,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f36,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))) ),
    inference(forward_demodulation,[],[f35,f32])).

fof(f35,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(forward_demodulation,[],[f34,f32])).

fof(f34,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f31,f32])).

fof(f31,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f15,f30,f17,f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f22,f17,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f21,f17,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f17,f25])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f17,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f17,f28])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f110,plain,
    ( spl7_4
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f58,f47,f40,f108])).

fof(f58,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f57,f41])).

fof(f57,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f50,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f50,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X4)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(superposition,[],[f48,f41])).

fof(f70,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f49,plain,
    ( spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f45,f40,f47])).

fof(f45,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f44,f41])).

fof(f44,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f43,f38])).

fof(f43,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))
    | ~ spl7_1 ),
    inference(superposition,[],[f41,f41])).

fof(f42,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f32,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:09:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (10255)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.44  % (10242)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (10244)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (10251)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (10241)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (10249)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (10245)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (10256)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (10248)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (10254)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (10248)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (10246)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f42,f49,f70,f110,f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f37,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X14)),X13)),X12)),X11))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f165,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X7)),X6)),X5))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f88,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1))) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f79,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))) ) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl7_3 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X1),X2))) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f78,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) ) | ~spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl7_1 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f77,f69])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f71,f41])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0))) ) | (~spl7_1 | ~spl7_3)),
% 0.20/0.49    inference(superposition,[],[f69,f41])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X5),X6),X7))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f87,f41])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),X5),k5_xboole_0(X6,k4_xboole_0(X7,X6))))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f86,f41])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X4,X7)),X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f85,f80])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),X6),X7),X4))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f84,f41])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X5),k5_xboole_0(X6,k4_xboole_0(X7,X6))),X4))) ) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f72,f41])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X6,X4,X8,X7,X5] : (k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X8,X4)),k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X7)),k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X5))),X4))) ) | (~spl7_2 | ~spl7_3)),
% 0.20/0.49    inference(superposition,[],[f69,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) ) | ~spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl7_2 <=> ! [X1,X3,X0,X2] : k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),X12),X13),X14))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f164,f41])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),X12),k5_xboole_0(X13,k4_xboole_0(X14,X13))))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f163,f41])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15)) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),X11),k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12))))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f162,f41])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(k5_xboole_0(X14,k4_xboole_0(X15,X14)),X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f161,f69])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),k4_xboole_0(k4_xboole_0(X15,X13),X14)),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f160,f41])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),k4_xboole_0(X15,k5_xboole_0(X13,k4_xboole_0(X14,X13)))),X12)),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f159,f69])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),k4_xboole_0(k4_xboole_0(X15,X12),k5_xboole_0(X13,k4_xboole_0(X14,X13)))),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f158,f41])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),k4_xboole_0(X15,k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)))),X11)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f157,f69])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k4_xboole_0(X15,X11),k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f124,f41])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X14,X12,X10,X15,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X10,X15)),k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)),k4_xboole_0(X15,k5_xboole_0(X11,k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(k5_xboole_0(X13,k4_xboole_0(X14,X13)),X12)),X11)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),X13),X14),X15))) ) | (~spl7_3 | ~spl7_4)),
% 0.20/0.49    inference(superposition,[],[f69,f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0)) ) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    spl7_4 <=> ! [X1,X3,X0,X2,X4] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)))),
% 0.20/0.49    inference(forward_demodulation,[],[f36,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))),
% 0.20/0.49    inference(forward_demodulation,[],[f35,f32])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),
% 0.20/0.49    inference(forward_demodulation,[],[f34,f32])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)))))),
% 0.20/0.49    inference(backward_demodulation,[],[f31,f32])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.20/0.49    inference(definition_unfolding,[],[f15,f30,f17,f28,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f16,f17])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f17,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f17,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f18,f17,f25])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f24,f17,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f23,f17,f28])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl7_4 | ~spl7_1 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f47,f40,f108])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X1),X2),X0)) ) | (~spl7_1 | ~spl7_2)),
% 0.20/0.49    inference(forward_demodulation,[],[f57,f41])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X4)))) ) | (~spl7_1 | ~spl7_2)),
% 0.20/0.49    inference(forward_demodulation,[],[f50,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f33,f32])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X4)))) ) | (~spl7_1 | ~spl7_2)),
% 0.20/0.49    inference(superposition,[],[f48,f41])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f68])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl7_2 | ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f40,f47])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) ) | ~spl7_1),
% 0.20/0.49    inference(forward_demodulation,[],[f44,f41])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)))) ) | ~spl7_1),
% 0.20/0.49    inference(forward_demodulation,[],[f43,f38])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ) | ~spl7_1),
% 0.20/0.49    inference(superposition,[],[f41,f41])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f40])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (10248)------------------------------
% 0.20/0.49  % (10248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10248)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (10248)Memory used [KB]: 6396
% 0.20/0.49  % (10248)Time elapsed: 0.091 s
% 0.20/0.49  % (10248)------------------------------
% 0.20/0.49  % (10248)------------------------------
% 0.20/0.49  % (10253)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (10240)Success in time 0.14 s
%------------------------------------------------------------------------------
