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
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u43,negated_conjecture,(
    ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u42,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u41,negated_conjecture,(
    r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) )).

tff(u40,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u39,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u38,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u37,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u36,negated_conjecture,(
    r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (23105)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.41  % (23114)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (23114)# SZS output start Saturation.
% 0.21/0.41  tff(u43,negated_conjecture,
% 0.21/0.41      ~v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u42,axiom,
% 0.21/0.41      (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u41,negated_conjecture,
% 0.21/0.41      r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u40,negated_conjecture,
% 0.21/0.41      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u39,negated_conjecture,
% 0.21/0.41      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u38,axiom,
% 0.21/0.41      (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u37,negated_conjecture,
% 0.21/0.41      ((~~r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.21/0.41  
% 0.21/0.41  tff(u36,negated_conjecture,
% 0.21/0.41      r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))).
% 0.21/0.41  
% 0.21/0.41  % (23114)# SZS output end Saturation.
% 0.21/0.41  % (23114)------------------------------
% 0.21/0.41  % (23114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (23114)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (23114)Memory used [KB]: 10490
% 0.21/0.41  % (23114)Time elapsed: 0.004 s
% 0.21/0.41  % (23114)------------------------------
% 0.21/0.41  % (23114)------------------------------
% 0.21/0.41  % (23099)Success in time 0.061 s
%------------------------------------------------------------------------------
