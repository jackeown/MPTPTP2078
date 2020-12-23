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
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u72,axiom,(
    ! [X3,X5,X2,X4] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK2(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) )).

tff(u71,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k4_waybel_0(sK0,sK1))
        | r1_tarski(X1,X2)
        | r2_hidden(sK2(X1,X2),X0)
        | ~ r1_tarski(sK1,X0) ) )).

tff(u70,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X1,X0] :
        ( ~ r1_tarski(X0,k4_waybel_0(sK0,sK1))
        | r2_hidden(sK2(X0,X1),sK1)
        | r1_tarski(X0,X1) ) )).

tff(u69,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X1,X3,X2] :
        ( ~ r1_tarski(sK1,X2)
        | r1_tarski(k4_waybel_0(sK0,sK1),X1)
        | r2_hidden(sK2(k4_waybel_0(sK0,sK1),X1),X3)
        | ~ r1_tarski(X2,X3) ) )).

% (5813)Refutation not found, incomplete strategy% (5813)------------------------------
% (5813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5813)Termination reason: Refutation not found, incomplete strategy

% (5813)Memory used [KB]: 9850
% (5813)Time elapsed: 0.061 s
% (5813)------------------------------
% (5813)------------------------------
tff(u68,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | r1_tarski(k4_waybel_0(sK0,sK1),sK1) )).

tff(u67,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X0] :
        ( r1_tarski(k4_waybel_0(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X0) ) )).

tff(u66,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u65,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u64,axiom,(
    ! [X1,X3,X0] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u63,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u62,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK2(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) )).

tff(u61,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X0] :
        ( r2_hidden(sK2(k4_waybel_0(sK0,sK1),X0),sK1)
        | r1_tarski(k4_waybel_0(sK0,sK1),X0) ) )).

tff(u60,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X1,X0] :
        ( r2_hidden(sK2(k4_waybel_0(sK0,sK1),X0),X1)
        | r1_tarski(k4_waybel_0(sK0,sK1),X0)
        | ~ r1_tarski(sK1,X1) ) )).

tff(u59,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u58,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u57,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) )).

tff(u56,negated_conjecture,
    ( ~ ~ v13_waybel_0(sK1,sK0)
    | ~ v13_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5826)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % (5826)Refutation not found, incomplete strategy% (5826)------------------------------
% 0.20/0.47  % (5826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5826)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5826)Memory used [KB]: 767
% 0.20/0.47  % (5826)Time elapsed: 0.006 s
% 0.20/0.47  % (5826)------------------------------
% 0.20/0.47  % (5826)------------------------------
% 0.20/0.47  % (5817)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.47  % (5813)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.47  % (5812)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (5817)# SZS output start Saturation.
% 0.20/0.47  tff(u72,axiom,
% 0.20/0.47      (![X3, X5, X2, X4] : ((~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK2(X2,X4),X5) | ~r1_tarski(X2,X3))))).
% 0.20/0.47  
% 0.20/0.47  tff(u71,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X1, X0, X2] : ((~r1_tarski(X1,k4_waybel_0(sK0,sK1)) | r1_tarski(X1,X2) | r2_hidden(sK2(X1,X2),X0) | ~r1_tarski(sK1,X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u70,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X1, X0] : ((~r1_tarski(X0,k4_waybel_0(sK0,sK1)) | r2_hidden(sK2(X0,X1),sK1) | r1_tarski(X0,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u69,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X1, X3, X2] : ((~r1_tarski(sK1,X2) | r1_tarski(k4_waybel_0(sK0,sK1),X1) | r2_hidden(sK2(k4_waybel_0(sK0,sK1),X1),X3) | ~r1_tarski(X2,X3)))))).
% 0.20/0.47  
% 0.20/0.47  % (5813)Refutation not found, incomplete strategy% (5813)------------------------------
% 0.20/0.47  % (5813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5813)Memory used [KB]: 9850
% 0.20/0.47  % (5813)Time elapsed: 0.061 s
% 0.20/0.47  % (5813)------------------------------
% 0.20/0.47  % (5813)------------------------------
% 0.20/0.47  tff(u68,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | r1_tarski(k4_waybel_0(sK0,sK1),sK1))).
% 0.20/0.47  
% 0.20/0.47  tff(u67,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X0] : ((r1_tarski(k4_waybel_0(sK0,sK1),X0) | ~r1_tarski(sK1,X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u66,axiom,
% 0.20/0.47      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u65,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u64,axiom,
% 0.20/0.47      (![X1, X3, X0] : ((~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u63,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u62,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((r2_hidden(sK2(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u61,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X0] : ((r2_hidden(sK2(k4_waybel_0(sK0,sK1),X0),sK1) | r1_tarski(k4_waybel_0(sK0,sK1),X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u60,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X1, X0] : ((r2_hidden(sK2(k4_waybel_0(sK0,sK1),X0),X1) | r1_tarski(k4_waybel_0(sK0,sK1),X0) | ~r1_tarski(sK1,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u59,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u58,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u57,negated_conjecture,
% 0.20/0.47      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u56,negated_conjecture,
% 0.20/0.47      ((~~v13_waybel_0(sK1,sK0)) | ~v13_waybel_0(sK1,sK0))).
% 0.20/0.47  
% 0.20/0.47  % (5817)# SZS output end Saturation.
% 0.20/0.47  % (5817)------------------------------
% 0.20/0.47  % (5817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5817)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (5817)Memory used [KB]: 5373
% 0.20/0.47  % (5817)Time elapsed: 0.005 s
% 0.20/0.47  % (5817)------------------------------
% 0.20/0.47  % (5817)------------------------------
% 0.20/0.47  % (5808)Success in time 0.119 s
%------------------------------------------------------------------------------
