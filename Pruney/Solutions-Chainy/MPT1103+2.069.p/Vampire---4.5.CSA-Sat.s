%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:43 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u161,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) )).

tff(u160,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0) ) )).

tff(u159,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u158,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u157,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

tff(u156,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u155,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u154,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u153,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) )).

tff(u152,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u151,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) )).

tff(u149,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u148,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u147,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 != X0 ) )).

tff(u146,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) )).

tff(u145,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) )).

tff(u144,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u143,axiom,(
    ! [X1,X0] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u142,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (1563)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (1571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.49  % (1563)Refutation not found, incomplete strategy% (1563)------------------------------
% 0.20/0.49  % (1563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (1563)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1563)Memory used [KB]: 10618
% 0.20/0.49  % (1563)Time elapsed: 0.062 s
% 0.20/0.49  % (1563)------------------------------
% 0.20/0.49  % (1563)------------------------------
% 0.20/0.49  % (1571)# SZS output start Saturation.
% 0.20/0.49  tff(u161,axiom,
% 0.20/0.49      (![X1, X0] : (((k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r1_tarski(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u160,axiom,
% 0.20/0.49      (![X0] : (((k1_xboole_0 != X0) | (k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u159,negated_conjecture,
% 0.20/0.49      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.20/0.49  
% 0.20/0.49  tff(u158,axiom,
% 0.20/0.49      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u157,axiom,
% 0.20/0.49      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u156,negated_conjecture,
% 0.20/0.49      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.49  
% 0.20/0.49  tff(u155,negated_conjecture,
% 0.20/0.49      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.49  
% 0.20/0.49  tff(u154,axiom,
% 0.20/0.49      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.49  
% 0.20/0.49  tff(u153,negated_conjecture,
% 0.20/0.49      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u152,negated_conjecture,
% 0.20/0.49      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.49  
% 0.20/0.49  tff(u151,negated_conjecture,
% 0.20/0.49      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 0.20/0.49  
% 0.20/0.49  tff(u150,axiom,
% 0.20/0.49      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u149,axiom,
% 0.20/0.49      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u148,axiom,
% 0.20/0.49      (![X1] : (r1_tarski(X1,X1)))).
% 0.20/0.49  
% 0.20/0.49  tff(u147,axiom,
% 0.20/0.49      (![X0] : ((r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 != X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u146,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u145,negated_conjecture,
% 0.20/0.49      ((~l1_struct_0(sK0)) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u144,negated_conjecture,
% 0.20/0.49      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u143,axiom,
% 0.20/0.49      (![X1, X0] : ((~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u142,negated_conjecture,
% 0.20/0.49      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  % (1571)# SZS output end Saturation.
% 0.20/0.49  % (1571)------------------------------
% 0.20/0.49  % (1571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1571)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (1571)Memory used [KB]: 10746
% 0.20/0.49  % (1571)Time elapsed: 0.070 s
% 0.20/0.49  % (1571)------------------------------
% 0.20/0.49  % (1571)------------------------------
% 0.20/0.50  % (1549)Success in time 0.137 s
%------------------------------------------------------------------------------
