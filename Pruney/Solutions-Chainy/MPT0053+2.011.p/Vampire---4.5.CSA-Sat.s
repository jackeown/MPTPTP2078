%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:57 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    3 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u18,negated_conjecture,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )).

tff(u17,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) )).

tff(u16,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) )).

tff(u15,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (12735)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (12733)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (12738)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.45  % (12730)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.45  % (12737)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.45  % (12730)# SZS output start Saturation.
% 0.22/0.45  tff(u18,negated_conjecture,
% 0.22/0.45      (k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))).
% 0.22/0.45  
% 0.22/0.45  tff(u17,axiom,
% 0.22/0.45      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1))))).
% 0.22/0.45  
% 0.22/0.45  tff(u16,axiom,
% 0.22/0.45      (![X1, X0] : ((k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)))))).
% 0.22/0.45  
% 0.22/0.45  tff(u15,axiom,
% 0.22/0.45      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 0.22/0.45  
% 0.22/0.45  % (12730)# SZS output end Saturation.
% 0.22/0.45  % (12730)------------------------------
% 0.22/0.45  % (12730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (12730)Termination reason: Satisfiable
% 0.22/0.45  
% 0.22/0.45  % (12730)Memory used [KB]: 6012
% 0.22/0.45  % (12730)Time elapsed: 0.033 s
% 0.22/0.45  % (12730)------------------------------
% 0.22/0.45  % (12730)------------------------------
% 0.22/0.45  % (12725)Success in time 0.086 s
%------------------------------------------------------------------------------
