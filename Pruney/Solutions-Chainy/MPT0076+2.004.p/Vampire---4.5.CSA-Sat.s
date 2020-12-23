%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:41 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u19,negated_conjecture,(
    ~ v1_xboole_0(sK1) )).

tff(u18,negated_conjecture,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0) ) )).

tff(u17,negated_conjecture,(
    r1_tarski(sK1,sK0) )).

tff(u16,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) )).

tff(u15,negated_conjecture,(
    r1_xboole_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30881)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.47  % (30894)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (30894)Refutation not found, incomplete strategy% (30894)------------------------------
% 0.21/0.47  % (30894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30894)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30894)Memory used [KB]: 767
% 0.21/0.47  % (30894)Time elapsed: 0.006 s
% 0.21/0.47  % (30894)------------------------------
% 0.21/0.47  % (30894)------------------------------
% 0.21/0.48  % (30886)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (30886)# SZS output start Saturation.
% 0.21/0.48  tff(u19,negated_conjecture,
% 0.21/0.48      ~v1_xboole_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  tff(u18,negated_conjecture,
% 0.21/0.48      (![X0] : ((~r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u17,negated_conjecture,
% 0.21/0.48      r1_tarski(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u16,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u15,negated_conjecture,
% 0.21/0.48      r1_xboole_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  % (30886)# SZS output end Saturation.
% 0.21/0.48  % (30886)------------------------------
% 0.21/0.48  % (30886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30886)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (30886)Memory used [KB]: 5245
% 0.21/0.48  % (30886)Time elapsed: 0.004 s
% 0.21/0.48  % (30886)------------------------------
% 0.21/0.48  % (30886)------------------------------
% 0.21/0.48  % (30878)Success in time 0.118 s
%------------------------------------------------------------------------------
