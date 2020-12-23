%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   71 (  71 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20763)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
tff(u85,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u84,axiom,(
    ! [X9,X5,X7,X8,X4,X6] :
      ( ~ r1_xboole_0(X8,k3_xboole_0(X7,X5))
      | ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X4,X5)
      | r1_xboole_0(X9,k3_xboole_0(X6,X4))
      | ~ r1_tarski(X9,X8) ) )).

tff(u83,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) )).

tff(u82,negated_conjecture,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X3,X1),sK2)
      | ~ r1_tarski(X2,X3)
      | r1_xboole_0(k3_xboole_0(X2,X0),sK0)
      | ~ r1_tarski(X0,X1) ) )).

tff(u81,negated_conjecture,(
    ~ r1_xboole_0(sK0,sK1) )).

tff(u80,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK2,sK2)
    | ~ r1_xboole_0(sK2,sK2) )).

tff(u79,negated_conjecture,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) )).

tff(u78,negated_conjecture,(
    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) )).

tff(u77,negated_conjecture,(
    ! [X7,X8,X6] :
      ( r1_xboole_0(k3_xboole_0(X7,X6),X8)
      | ~ r1_tarski(X7,sK1)
      | ~ r1_tarski(X8,sK0)
      | ~ r1_tarski(X6,sK2) ) )).

tff(u76,negated_conjecture,(
    ! [X1,X0,X2] :
      ( r1_xboole_0(X2,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X1,sK2)
      | ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X2,sK0) ) )).

tff(u75,negated_conjecture,(
    ! [X1,X3,X5,X0,X2,X4] :
      ( ~ r1_tarski(X5,X2)
      | ~ r1_tarski(X1,sK1)
      | ~ r1_tarski(X2,sK0)
      | ~ r1_tarski(X3,X1)
      | ~ r1_tarski(X4,X0)
      | r1_xboole_0(X5,k3_xboole_0(X3,X4))
      | ~ r1_tarski(X0,sK2) ) )).

tff(u74,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | r1_xboole_0(X1,sK0)
      | ~ r1_xboole_0(X0,sK2) ) )).

tff(u73,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) )).

tff(u72,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r1_tarski(X1,sK0)
      | ~ r1_tarski(X0,sK1)
      | r1_xboole_0(X0,X1) ) )).

tff(u71,negated_conjecture,(
    ! [X9,X11,X10] :
      ( ~ r1_tarski(k3_xboole_0(X11,k3_xboole_0(X10,X9)),sK0)
      | ~ r1_tarski(X10,sK1)
      | ~ r1_tarski(X9,sK2)
      | r1_xboole_0(X11,k3_xboole_0(X10,X9)) ) )).

tff(u70,negated_conjecture,(
    ! [X9,X11,X5,X7,X8,X10,X4,X6] :
      ( ~ r1_tarski(k3_xboole_0(X5,X6),sK0)
      | ~ r1_tarski(X4,sK1)
      | ~ r1_tarski(X7,X4)
      | ~ r1_tarski(X8,X9)
      | r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X7,X8))
      | ~ r1_tarski(X9,sK2)
      | ~ r1_tarski(X11,X6)
      | ~ r1_tarski(X10,X5) ) )).

tff(u69,negated_conjecture,(
    ! [X9,X11,X13,X15,X10,X12,X14] :
      ( ~ r1_tarski(k3_xboole_0(X10,X11),sK0)
      | ~ r1_tarski(X9,sK1)
      | ~ r1_tarski(X12,sK2)
      | ~ r1_tarski(X13,X10)
      | ~ r1_tarski(X14,X11)
      | r1_xboole_0(X15,k3_xboole_0(X13,X14))
      | ~ r1_tarski(X15,k3_xboole_0(X9,X12)) ) )).

tff(u68,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0) )).

tff(u67,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK2,sK0) )).

tff(u66,negated_conjecture,(
    r1_tarski(sK0,sK2) )).

tff(u65,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (20766)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  % (20758)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (20774)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.47  % (20764)WARNING: option uwaf not known.
% 0.21/0.47  % (20764)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.47  % (20764)Refutation not found, incomplete strategy% (20764)------------------------------
% 0.21/0.47  % (20764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20764)Memory used [KB]: 895
% 0.21/0.47  % (20764)Time elapsed: 0.072 s
% 0.21/0.47  % (20764)------------------------------
% 0.21/0.47  % (20764)------------------------------
% 0.21/0.48  % (20757)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  % (20767)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (20760)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (20759)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (20771)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.49  % (20773)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (20768)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (20754)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (20754)Refutation not found, incomplete strategy% (20754)------------------------------
% 0.21/0.49  % (20754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20754)Memory used [KB]: 5373
% 0.21/0.49  % (20754)Time elapsed: 0.053 s
% 0.21/0.49  % (20754)------------------------------
% 0.21/0.49  % (20754)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (20773)# SZS output start Saturation.
% 0.21/0.49  % (20763)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  tff(u85,axiom,
% 0.21/0.49      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u84,axiom,
% 0.21/0.49      (![X9, X5, X7, X8, X4, X6] : ((~r1_xboole_0(X8,k3_xboole_0(X7,X5)) | ~r1_tarski(X6,X7) | ~r1_tarski(X4,X5) | r1_xboole_0(X9,k3_xboole_0(X6,X4)) | ~r1_tarski(X9,X8))))).
% 0.21/0.49  
% 0.21/0.49  tff(u83,axiom,
% 0.21/0.49      (![X1, X0] : ((~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u82,negated_conjecture,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~r1_xboole_0(k3_xboole_0(X3,X1),sK2) | ~r1_tarski(X2,X3) | r1_xboole_0(k3_xboole_0(X2,X0),sK0) | ~r1_tarski(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u81,negated_conjecture,
% 0.21/0.49      ~r1_xboole_0(sK0,sK1)).
% 0.21/0.49  
% 0.21/0.49  tff(u80,negated_conjecture,
% 0.21/0.49      ((~~r1_xboole_0(sK2,sK2)) | ~r1_xboole_0(sK2,sK2))).
% 0.21/0.49  
% 0.21/0.49  tff(u79,negated_conjecture,
% 0.21/0.49      r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))).
% 0.21/0.49  
% 0.21/0.49  tff(u78,negated_conjecture,
% 0.21/0.49      r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u77,negated_conjecture,
% 0.21/0.49      (![X7, X8, X6] : ((r1_xboole_0(k3_xboole_0(X7,X6),X8) | ~r1_tarski(X7,sK1) | ~r1_tarski(X8,sK0) | ~r1_tarski(X6,sK2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u76,negated_conjecture,
% 0.21/0.49      (![X1, X0, X2] : ((r1_xboole_0(X2,k3_xboole_0(X0,X1)) | ~r1_tarski(X1,sK2) | ~r1_tarski(X0,sK1) | ~r1_tarski(X2,sK0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u75,negated_conjecture,
% 0.21/0.49      (![X1, X3, X5, X0, X2, X4] : ((~r1_tarski(X5,X2) | ~r1_tarski(X1,sK1) | ~r1_tarski(X2,sK0) | ~r1_tarski(X3,X1) | ~r1_tarski(X4,X0) | r1_xboole_0(X5,k3_xboole_0(X3,X4)) | ~r1_tarski(X0,sK2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u74,negated_conjecture,
% 0.21/0.49      (![X1, X0] : ((~r1_tarski(X1,X0) | r1_xboole_0(X1,sK0) | ~r1_xboole_0(X0,sK2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u73,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u72,negated_conjecture,
% 0.21/0.49      (![X1, X0] : ((~r1_tarski(X1,sK2) | ~r1_tarski(X1,sK0) | ~r1_tarski(X0,sK1) | r1_xboole_0(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u71,negated_conjecture,
% 0.21/0.49      (![X9, X11, X10] : ((~r1_tarski(k3_xboole_0(X11,k3_xboole_0(X10,X9)),sK0) | ~r1_tarski(X10,sK1) | ~r1_tarski(X9,sK2) | r1_xboole_0(X11,k3_xboole_0(X10,X9)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u70,negated_conjecture,
% 0.21/0.49      (![X9, X11, X5, X7, X8, X10, X4, X6] : ((~r1_tarski(k3_xboole_0(X5,X6),sK0) | ~r1_tarski(X4,sK1) | ~r1_tarski(X7,X4) | ~r1_tarski(X8,X9) | r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X7,X8)) | ~r1_tarski(X9,sK2) | ~r1_tarski(X11,X6) | ~r1_tarski(X10,X5))))).
% 0.21/0.49  
% 0.21/0.49  tff(u69,negated_conjecture,
% 0.21/0.49      (![X9, X11, X13, X15, X10, X12, X14] : ((~r1_tarski(k3_xboole_0(X10,X11),sK0) | ~r1_tarski(X9,sK1) | ~r1_tarski(X12,sK2) | ~r1_tarski(X13,X10) | ~r1_tarski(X14,X11) | r1_xboole_0(X15,k3_xboole_0(X13,X14)) | ~r1_tarski(X15,k3_xboole_0(X9,X12)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u68,negated_conjecture,
% 0.21/0.49      ((~~r1_tarski(sK0,sK0)) | ~r1_tarski(sK0,sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u67,negated_conjecture,
% 0.21/0.49      ((~~r1_tarski(sK2,sK0)) | ~r1_tarski(sK2,sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u66,negated_conjecture,
% 0.21/0.49      r1_tarski(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u65,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  % (20773)# SZS output end Saturation.
% 0.21/0.49  % (20773)------------------------------
% 0.21/0.49  % (20773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20773)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (20773)Memory used [KB]: 5373
% 0.21/0.49  % (20773)Time elapsed: 0.079 s
% 0.21/0.49  % (20773)------------------------------
% 0.21/0.49  % (20773)------------------------------
% 0.21/0.49  % (20753)Success in time 0.132 s
%------------------------------------------------------------------------------
