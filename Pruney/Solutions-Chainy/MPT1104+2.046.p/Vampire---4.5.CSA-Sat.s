%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:56 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  47 expanded)
%              Number of leaves         :   47 (  47 expanded)
%              Depth                    :    0
%              Number of atoms          :   78 (  78 expanded)
%              Number of equality atoms :   60 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u313,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u312,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

tff(u311,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

tff(u310,negated_conjecture,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(sK1,sK2))
    | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)) )).

tff(u309,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

tff(u308,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u307,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

tff(u306,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u305,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

tff(u304,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u303,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

tff(u302,axiom,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

tff(u301,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u300,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u299,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u298,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) )).

tff(u297,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k3_tarski(k2_tarski(sK1,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) )).

tff(u296,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k3_tarski(k2_tarski(sK2,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) )).

tff(u295,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u294,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u293,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u292,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u291,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1) )).

tff(u290,axiom,(
    ! [X5,X4] : k7_subset_1(X4,X4,X5) = k7_subset_1(k3_tarski(k2_tarski(X4,X5)),k3_tarski(k2_tarski(X4,X5)),X5) )).

tff(u289,axiom,(
    ! [X7,X6] : k7_subset_1(X7,X7,X6) = k7_subset_1(k3_tarski(k2_tarski(X6,X7)),k3_tarski(k2_tarski(X6,X7)),X6) )).

tff(u288,axiom,(
    ! [X1,X0] : k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))) )).

tff(u287,axiom,(
    ! [X1,X0] : k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0))))) )).

tff(u286,axiom,(
    ! [X1,X0] : k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

tff(u285,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u284,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u283,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u282,negated_conjecture,
    ( sK1 != k7_subset_1(sK1,sK1,sK2)
    | sK1 = k7_subset_1(sK1,sK1,sK2) )).

tff(u281,negated_conjecture,
    ( sK1 != k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)
    | sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

tff(u280,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))
    | sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) )).

tff(u279,negated_conjecture,
    ( sK2 != k7_subset_1(sK2,sK2,sK1)
    | sK2 = k7_subset_1(sK2,sK2,sK1) )).

tff(u278,negated_conjecture,
    ( sK2 != k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u277,negated_conjecture,
    ( sK2 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) )).

tff(u276,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) )).

tff(u275,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u274,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2)) ) )).

tff(u273,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u272,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u271,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u270,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u269,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u268,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u267,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (25178)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (25178)Refutation not found, incomplete strategy% (25178)------------------------------
% 0.20/0.52  % (25178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25178)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25178)Memory used [KB]: 10618
% 0.20/0.52  % (25178)Time elapsed: 0.104 s
% 0.20/0.52  % (25178)------------------------------
% 0.20/0.52  % (25178)------------------------------
% 0.20/0.52  % (25184)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (25168)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (25170)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (25192)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (25172)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (25179)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (25170)Refutation not found, incomplete strategy% (25170)------------------------------
% 0.20/0.52  % (25170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25170)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25170)Memory used [KB]: 10746
% 0.20/0.52  % (25170)Time elapsed: 0.115 s
% 0.20/0.52  % (25170)------------------------------
% 0.20/0.52  % (25170)------------------------------
% 0.20/0.53  % (25179)Refutation not found, incomplete strategy% (25179)------------------------------
% 0.20/0.53  % (25179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25179)Memory used [KB]: 10746
% 0.20/0.53  % (25179)Time elapsed: 0.114 s
% 0.20/0.53  % (25179)------------------------------
% 0.20/0.53  % (25179)------------------------------
% 0.20/0.53  % (25190)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (25169)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (25172)Refutation not found, incomplete strategy% (25172)------------------------------
% 0.20/0.53  % (25172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (25184)# SZS output start Saturation.
% 0.20/0.53  tff(u313,negated_conjecture,
% 0.20/0.53      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u312,axiom,
% 0.20/0.53      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u311,axiom,
% 0.20/0.53      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u310,negated_conjecture,
% 0.20/0.53      ((~(k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)))) | (k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u309,axiom,
% 0.20/0.53      (![X1] : ((k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u308,axiom,
% 0.20/0.53      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u307,axiom,
% 0.20/0.53      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u306,axiom,
% 0.20/0.53      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u305,axiom,
% 0.20/0.53      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u304,axiom,
% 0.20/0.53      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u303,axiom,
% 0.20/0.53      (![X0] : ((k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u302,axiom,
% 0.20/0.53      (![X0] : ((k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u301,negated_conjecture,
% 0.20/0.53      ((~(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u300,negated_conjecture,
% 0.20/0.53      ((~(k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u299,axiom,
% 0.20/0.53      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u298,axiom,
% 0.20/0.53      (![X0] : ((k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u297,negated_conjecture,
% 0.20/0.53      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u296,negated_conjecture,
% 0.20/0.53      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u295,negated_conjecture,
% 0.20/0.53      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u294,negated_conjecture,
% 0.20/0.53      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u293,axiom,
% 0.20/0.53      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u292,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u291,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u290,axiom,
% 0.20/0.53      (![X5, X4] : ((k7_subset_1(X4,X4,X5) = k7_subset_1(k3_tarski(k2_tarski(X4,X5)),k3_tarski(k2_tarski(X4,X5)),X5))))).
% 0.20/0.53  
% 0.20/0.53  tff(u289,axiom,
% 0.20/0.53      (![X7, X6] : ((k7_subset_1(X7,X7,X6) = k7_subset_1(k3_tarski(k2_tarski(X6,X7)),k3_tarski(k2_tarski(X6,X7)),X6))))).
% 0.20/0.53  
% 0.20/0.53  tff(u288,axiom,
% 0.20/0.53      (![X1, X0] : ((k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u287,axiom,
% 0.20/0.53      (![X1, X0] : ((k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0))))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u286,axiom,
% 0.20/0.53      (![X1, X0] : ((k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u285,negated_conjecture,
% 0.20/0.53      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 0.20/0.53  
% 0.20/0.53  tff(u284,negated_conjecture,
% 0.20/0.53      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u283,negated_conjecture,
% 0.20/0.53      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u282,negated_conjecture,
% 0.20/0.53      ((~(sK1 = k7_subset_1(sK1,sK1,sK2))) | (sK1 = k7_subset_1(sK1,sK1,sK2)))).
% 0.20/0.53  
% 0.20/0.53  tff(u281,negated_conjecture,
% 0.20/0.53      ((~(sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2))) | (sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)))).
% 0.20/0.53  
% 0.20/0.53  tff(u280,negated_conjecture,
% 0.20/0.53      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u279,negated_conjecture,
% 0.20/0.53      ((~(sK2 = k7_subset_1(sK2,sK2,sK1))) | (sK2 = k7_subset_1(sK2,sK2,sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u278,negated_conjecture,
% 0.20/0.53      ((~(sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u277,negated_conjecture,
% 0.20/0.53      ((~(sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))))) | (sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u276,axiom,
% 0.20/0.53      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u275,negated_conjecture,
% 0.20/0.53      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 0.20/0.53  
% 0.20/0.53  tff(u274,axiom,
% 0.20/0.53      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u273,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u272,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u271,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u270,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u269,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u268,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u267,axiom,
% 0.20/0.53      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.53  
% 0.20/0.53  % (25184)# SZS output end Saturation.
% 0.20/0.53  % (25184)------------------------------
% 0.20/0.53  % (25184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25184)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (25184)Memory used [KB]: 10874
% 0.20/0.53  % (25184)Time elapsed: 0.120 s
% 0.20/0.53  % (25184)------------------------------
% 0.20/0.53  % (25184)------------------------------
% 0.20/0.53  % (25167)Success in time 0.169 s
%------------------------------------------------------------------------------
