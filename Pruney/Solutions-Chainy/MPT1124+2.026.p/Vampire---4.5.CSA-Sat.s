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
% DateTime   : Thu Dec  3 13:09:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u116,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
          | r2_hidden(X0,X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) )).

tff(u115,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(X0,X1)
          | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) )
    | ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) ) )).

tff(u114,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(X0,X1)
          | m1_subset_1(X0,X1) )
    | ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) )).

tff(u113,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u112,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
          | r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) ) )).

tff(u111,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0)
          | ~ l1_pre_topc(X0) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) )).

tff(u110,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u109,axiom,
    ( ~ ! [X1,X0] :
          ( ~ l1_pre_topc(X0)
          | ~ m1_pre_topc(X1,X0)
          | l1_pre_topc(X1) )
    | ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) )).

tff(u108,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK0) )).

tff(u107,negated_conjecture,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK1) )).

tff(u106,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_pre_topc(X0,sK0)
          | l1_pre_topc(X0) )
    | ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) )).

tff(u105,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_pre_topc(X0,sK1)
          | l1_pre_topc(X0) )
    | ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | l1_pre_topc(X0) ) )).

tff(u104,negated_conjecture,
    ( ~ m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (9760)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (9760)# SZS output start Saturation.
% 0.21/0.46  tff(u116,axiom,
% 0.21/0.46      ((~(![X1, X0] : ((~r1_tarski(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1))))) | (![X1, X0] : ((~r1_tarski(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u115,axiom,
% 0.21/0.46      ((~(![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)))))) | (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u114,axiom,
% 0.21/0.46      ((~(![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))) | (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u113,negated_conjecture,
% 0.21/0.46      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u112,axiom,
% 0.21/0.46      ((~(![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))) | (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u111,axiom,
% 0.21/0.46      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u110,negated_conjecture,
% 0.21/0.46      ((~m1_subset_1(sK2,u1_struct_0(sK1))) | m1_subset_1(sK2,u1_struct_0(sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u109,axiom,
% 0.21/0.46      ((~(![X1, X0] : ((~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))))) | (![X1, X0] : ((~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u108,negated_conjecture,
% 0.21/0.46      ((~l1_pre_topc(sK0)) | l1_pre_topc(sK0))).
% 0.21/0.46  
% 0.21/0.46  tff(u107,negated_conjecture,
% 0.21/0.46      ((~l1_pre_topc(sK1)) | l1_pre_topc(sK1))).
% 0.21/0.46  
% 0.21/0.46  tff(u106,negated_conjecture,
% 0.21/0.46      ((~(![X0] : ((~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))))) | (![X0] : ((~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u105,negated_conjecture,
% 0.21/0.46      ((~(![X0] : ((~m1_pre_topc(X0,sK1) | l1_pre_topc(X0))))) | (![X0] : ((~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u104,negated_conjecture,
% 0.21/0.46      ((~m1_pre_topc(sK1,sK0)) | m1_pre_topc(sK1,sK0))).
% 0.21/0.46  
% 0.21/0.46  % (9760)# SZS output end Saturation.
% 0.21/0.46  % (9760)------------------------------
% 0.21/0.46  % (9760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9760)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (9760)Memory used [KB]: 6140
% 0.21/0.46  % (9760)Time elapsed: 0.056 s
% 0.21/0.46  % (9760)------------------------------
% 0.21/0.46  % (9760)------------------------------
% 0.21/0.46  % (9752)Success in time 0.108 s
%------------------------------------------------------------------------------
