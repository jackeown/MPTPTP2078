%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:24 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u66,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) )).

tff(u63,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k1_enumset1(X0,X0,X1),X2) ) )).

tff(u62,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) ) )).

tff(u61,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) )).

tff(u60,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u59,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u58,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u57,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) )).

tff(u55,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u54,negated_conjecture,(
    l1_pre_topc(sK1) )).

tff(u53,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) )).

tff(u52,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) )).

tff(u51,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (17374)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (17388)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (17388)# SZS output start Saturation.
% 0.20/0.48  tff(u66,axiom,
% 0.20/0.48      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u65,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u64,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u63,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k1_enumset1(X0,X0,X1),X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u62,axiom,
% 0.20/0.48      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u61,axiom,
% 0.20/0.48      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u60,negated_conjecture,
% 0.20/0.48      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u59,axiom,
% 0.20/0.48      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u58,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u57,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u56,axiom,
% 0.20/0.48      (![X1, X0] : ((~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u55,negated_conjecture,
% 0.20/0.48      l1_pre_topc(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u54,negated_conjecture,
% 0.20/0.48      l1_pre_topc(sK1)).
% 0.20/0.48  
% 0.20/0.48  tff(u53,negated_conjecture,
% 0.20/0.48      (![X0] : ((~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u52,negated_conjecture,
% 0.20/0.48      (![X0] : ((~m1_pre_topc(X0,sK1) | l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u51,negated_conjecture,
% 0.20/0.48      m1_pre_topc(sK1,sK0)).
% 0.20/0.48  
% 0.20/0.48  % (17388)# SZS output end Saturation.
% 0.20/0.48  % (17388)------------------------------
% 0.20/0.48  % (17388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17388)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (17388)Memory used [KB]: 6140
% 0.20/0.48  % (17388)Time elapsed: 0.045 s
% 0.20/0.48  % (17388)------------------------------
% 0.20/0.48  % (17388)------------------------------
% 0.20/0.48  % (17373)Success in time 0.121 s
%------------------------------------------------------------------------------
