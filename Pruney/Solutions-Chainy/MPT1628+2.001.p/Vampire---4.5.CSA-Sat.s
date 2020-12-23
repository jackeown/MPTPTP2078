%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:55 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u42,negated_conjecture,(
    r1_tarski(sK3,sK4) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u40,negated_conjecture,
    ( ~ ~ r2_waybel_0(sK1,sK2,sK4)
    | ~ r2_waybel_0(sK1,sK2,sK4) )).

tff(u39,negated_conjecture,
    ( ~ r2_waybel_0(sK1,sK2,sK3)
    | r2_waybel_0(sK1,sK2,sK3) )).

tff(u38,negated_conjecture,
    ( ~ ~ sP0(sK4,sK2,sK1,sK3)
    | ~ sP0(sK4,sK2,sK1,sK3) )).

tff(u37,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r1_waybel_0(X2,X1,X0) ) )).

tff(u36,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_waybel_0(X2,X1,X3) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (14755)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  % (14755)Refutation not found, incomplete strategy% (14755)------------------------------
% 0.21/0.46  % (14755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14747)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (14755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14755)Memory used [KB]: 767
% 0.21/0.47  % (14755)Time elapsed: 0.047 s
% 0.21/0.47  % (14755)------------------------------
% 0.21/0.47  % (14755)------------------------------
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (14747)# SZS output start Saturation.
% 0.21/0.47  tff(u42,negated_conjecture,
% 0.21/0.47      r1_tarski(sK3,sK4)).
% 0.21/0.47  
% 0.21/0.47  tff(u41,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u40,negated_conjecture,
% 0.21/0.47      ((~~r2_waybel_0(sK1,sK2,sK4)) | ~r2_waybel_0(sK1,sK2,sK4))).
% 0.21/0.47  
% 0.21/0.47  tff(u39,negated_conjecture,
% 0.21/0.47      ((~r2_waybel_0(sK1,sK2,sK3)) | r2_waybel_0(sK1,sK2,sK3))).
% 0.21/0.47  
% 0.21/0.47  tff(u38,negated_conjecture,
% 0.21/0.47      ((~~sP0(sK4,sK2,sK1,sK3)) | ~sP0(sK4,sK2,sK1,sK3))).
% 0.21/0.47  
% 0.21/0.47  tff(u37,axiom,
% 0.21/0.47      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | ~r1_waybel_0(X2,X1,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u36,axiom,
% 0.21/0.47      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | r1_waybel_0(X2,X1,X3))))).
% 0.21/0.47  
% 0.21/0.47  % (14747)# SZS output end Saturation.
% 0.21/0.47  % (14747)------------------------------
% 0.21/0.47  % (14747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14747)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (14747)Memory used [KB]: 5373
% 0.21/0.47  % (14747)Time elapsed: 0.045 s
% 0.21/0.47  % (14747)------------------------------
% 0.21/0.47  % (14747)------------------------------
% 0.21/0.47  % (14753)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (14739)Success in time 0.107 s
%------------------------------------------------------------------------------
