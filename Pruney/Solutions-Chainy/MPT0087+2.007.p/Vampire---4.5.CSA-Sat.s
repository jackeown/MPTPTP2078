%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:28 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u24,axiom,(
    ! [X1,X3,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X3)
      | ~ sP3(X3,X0) ) )).

tff(u23,axiom,(
    ! [X3,X0,X2] :
      ( ~ r1_tarski(X2,X3)
      | r1_xboole_0(X0,X2)
      | sP3(X3,X0) ) )).

tff(u22,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u21,negated_conjecture,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) )).

tff(u20,negated_conjecture,(
    r1_xboole_0(sK0,sK1) )).

tff(u19,axiom,(
    ! [X1,X0,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | sP3(X1,X0) ) )).

tff(u18,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u17,negated_conjecture,(
    sP3(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (26317)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.46  % (26326)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.47  % (26330)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.48  % (26320)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.48  % (26328)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (26318)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (26327)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (26316)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.49  % (26322)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (26313)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (26313)Refutation not found, incomplete strategy% (26313)------------------------------
% 0.22/0.49  % (26313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26313)Memory used [KB]: 5245
% 0.22/0.49  % (26313)Time elapsed: 0.057 s
% 0.22/0.49  % (26313)------------------------------
% 0.22/0.49  % (26313)------------------------------
% 0.22/0.49  % (26323)WARNING: option uwaf not known.
% 0.22/0.50  % (26319)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (26319)# SZS output start Saturation.
% 0.22/0.50  tff(u24,axiom,
% 0.22/0.50      (![X1, X3, X0] : ((~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X3) | ~sP3(X3,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u23,axiom,
% 0.22/0.50      (![X3, X0, X2] : ((~r1_tarski(X2,X3) | r1_xboole_0(X0,X2) | sP3(X3,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u22,axiom,
% 0.22/0.50      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u21,negated_conjecture,
% 0.22/0.50      ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))).
% 0.22/0.50  
% 0.22/0.50  tff(u20,negated_conjecture,
% 0.22/0.50      r1_xboole_0(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  tff(u19,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((r1_xboole_0(X0,k4_xboole_0(X1,X2)) | sP3(X1,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u18,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~sP3(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u17,negated_conjecture,
% 0.22/0.50      sP3(sK1,sK0)).
% 0.22/0.50  
% 0.22/0.50  % (26319)# SZS output end Saturation.
% 0.22/0.50  % (26319)------------------------------
% 0.22/0.50  % (26319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26319)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (26319)Memory used [KB]: 5245
% 0.22/0.50  % (26319)Time elapsed: 0.051 s
% 0.22/0.50  % (26319)------------------------------
% 0.22/0.50  % (26319)------------------------------
% 0.22/0.50  % (26310)Success in time 0.137 s
%------------------------------------------------------------------------------
