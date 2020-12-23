%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  50 expanded)
%              Number of leaves         :   50 (  50 expanded)
%              Depth                    :    0
%              Number of atoms          :  102 ( 102 expanded)
%              Number of equality atoms :   58 (  58 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u262,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u261,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 )).

tff(u260,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u259,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u258,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u257,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

% (2766)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
tff(u256,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u255,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u254,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u253,axiom,(
    ! [X3,X4] :
      ( k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X4)
      | k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3)
      | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) ) )).

tff(u252,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u251,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u250,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) )).

tff(u249,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u248,axiom,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 )).

tff(u247,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u246,negated_conjecture,(
    sK1 = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))) )).

tff(u245,axiom,(
    ! [X1,X0] :
      ( sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1))
      | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ) )).

tff(u244,axiom,(
    ! [X1,X0] :
      ( sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0))
      | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ) )).

tff(u243,axiom,(
    ! [X1,X2] :
      ( sK2(X1,k1_zfmisc_1(X2)) = k1_setfam_1(k2_enumset1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X2))
      | sK2(X1,k1_zfmisc_1(X2)) = k1_setfam_1(k2_enumset1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1))
      | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) ) )).

tff(u242,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ) )).

tff(u241,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u240,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X2,sK2(X2,X3))
      | k1_zfmisc_1(X2) = X3
      | sK2(X2,X3) = X2
      | r2_hidden(sK2(X2,X3),X3) ) )).

tff(u239,axiom,(
    ! [X3,X4] :
      ( ~ r1_tarski(X3,sK2(X3,k1_zfmisc_1(X4)))
      | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X4))
      | sK2(X3,k1_zfmisc_1(X4)) = X3
      | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) ) )).

tff(u238,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X2,sK2(X2,k1_zfmisc_1(X3)))
      | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
      | sK2(X2,k1_zfmisc_1(X3)) = X2
      | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) ) )).

tff(u237,axiom,(
    ! [X5,X4] :
      ( ~ r1_tarski(X5,sK2(X4,k1_zfmisc_1(X5)))
      | sK2(X4,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(sK2(X4,k1_zfmisc_1(X5)),sK2(X4,k1_zfmisc_1(X5)),sK2(X4,k1_zfmisc_1(X5)),X4))
      | sK2(X4,k1_zfmisc_1(X5)) = X5
      | k1_zfmisc_1(X4) = k1_zfmisc_1(X5) ) )).

tff(u236,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X3,sK2(X2,k1_zfmisc_1(X3)))
      | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
      | sK2(X2,k1_zfmisc_1(X3)) = X3
      | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2) ) )).

tff(u235,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u234,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u233,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
      | ~ r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) ) )).

tff(u232,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u231,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u230,axiom,(
    ! [X1,X0] :
      ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
      | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1)) ) )).

tff(u229,axiom,(
    ! [X1,X0] :
      ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
      | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0)) ) )).

tff(u228,axiom,(
    ! [X1,X0] :
      ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
      | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ) )).

tff(u227,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) )).

tff(u226,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r1_tarski(sK2(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) )).

tff(u225,axiom,(
    ! [X3,X0] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) )).

tff(u224,axiom,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) )).

tff(u223,negated_conjecture,(
    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u222,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_zfmisc_1(X0) = X1
      | sK2(X0,X1) = k1_setfam_1(k2_enumset1(sK2(X0,X1),sK2(X0,X1),sK2(X0,X1),X0)) ) )).

tff(u221,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(sK2(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) )).

tff(u220,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u219,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u218,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u217,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u216,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u215,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u214,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) )).

tff(u213,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (2750)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (2759)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (2767)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (2756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2752)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (2753)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2759)Refutation not found, incomplete strategy% (2759)------------------------------
% 0.21/0.53  % (2759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2767)Refutation not found, incomplete strategy% (2767)------------------------------
% 0.21/0.53  % (2767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2767)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2767)Memory used [KB]: 1663
% 0.21/0.53  % (2767)Time elapsed: 0.116 s
% 0.21/0.53  % (2767)------------------------------
% 0.21/0.53  % (2767)------------------------------
% 0.21/0.53  % (2759)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2759)Memory used [KB]: 1791
% 0.21/0.53  % (2759)Time elapsed: 0.120 s
% 0.21/0.53  % (2759)------------------------------
% 0.21/0.53  % (2759)------------------------------
% 0.21/0.53  % (2765)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (2755)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (2754)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (2764)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (2764)Refutation not found, incomplete strategy% (2764)------------------------------
% 0.21/0.54  % (2764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2764)Memory used [KB]: 1663
% 0.21/0.54  % (2764)Time elapsed: 0.130 s
% 0.21/0.54  % (2764)------------------------------
% 0.21/0.54  % (2764)------------------------------
% 0.21/0.54  % (2751)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2769)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (2755)Refutation not found, incomplete strategy% (2755)------------------------------
% 0.21/0.54  % (2755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2755)Memory used [KB]: 1791
% 0.21/0.54  % (2755)Time elapsed: 0.131 s
% 0.21/0.54  % (2755)------------------------------
% 0.21/0.54  % (2755)------------------------------
% 0.21/0.54  % (2751)Refutation not found, incomplete strategy% (2751)------------------------------
% 0.21/0.54  % (2751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2751)Memory used [KB]: 1663
% 0.21/0.54  % (2751)Time elapsed: 0.122 s
% 0.21/0.54  % (2751)------------------------------
% 0.21/0.54  % (2751)------------------------------
% 0.21/0.54  % (2773)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (2776)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (2776)Refutation not found, incomplete strategy% (2776)------------------------------
% 0.21/0.54  % (2776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2776)Memory used [KB]: 6268
% 0.21/0.54  % (2776)Time elapsed: 0.131 s
% 0.21/0.54  % (2776)------------------------------
% 0.21/0.54  % (2776)------------------------------
% 0.21/0.54  % (2774)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (2772)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (2778)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (2779)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (2774)Refutation not found, incomplete strategy% (2774)------------------------------
% 0.21/0.54  % (2774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2774)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2774)Memory used [KB]: 10618
% 0.21/0.54  % (2774)Time elapsed: 0.139 s
% 0.21/0.54  % (2774)------------------------------
% 0.21/0.54  % (2774)------------------------------
% 0.21/0.54  % (2779)Refutation not found, incomplete strategy% (2779)------------------------------
% 0.21/0.54  % (2779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2779)Memory used [KB]: 1663
% 0.21/0.54  % (2779)Time elapsed: 0.002 s
% 0.21/0.54  % (2779)------------------------------
% 0.21/0.54  % (2779)------------------------------
% 0.21/0.54  % (2768)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (2778)Refutation not found, incomplete strategy% (2778)------------------------------
% 0.21/0.54  % (2778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2778)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2778)Memory used [KB]: 10746
% 0.21/0.54  % (2778)Time elapsed: 0.137 s
% 0.21/0.54  % (2778)------------------------------
% 0.21/0.54  % (2778)------------------------------
% 0.21/0.54  % (2772)Refutation not found, incomplete strategy% (2772)------------------------------
% 0.21/0.54  % (2772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2772)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2772)Memory used [KB]: 6268
% 0.21/0.54  % (2772)Time elapsed: 0.141 s
% 0.21/0.54  % (2772)------------------------------
% 0.21/0.54  % (2772)------------------------------
% 0.21/0.54  % (2768)Refutation not found, incomplete strategy% (2768)------------------------------
% 0.21/0.54  % (2768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2768)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2768)Memory used [KB]: 1663
% 0.21/0.54  % (2768)Time elapsed: 0.136 s
% 0.21/0.54  % (2768)------------------------------
% 0.21/0.54  % (2768)------------------------------
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (2756)# SZS output start Saturation.
% 0.21/0.55  tff(u262,negated_conjecture,
% 0.21/0.55      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.55  
% 0.21/0.55  tff(u261,axiom,
% 0.21/0.55      (![X0] : ((k5_xboole_0(X0,X0) = k1_xboole_0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u260,axiom,
% 0.21/0.55      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.55  
% 0.21/0.55  tff(u259,axiom,
% 0.21/0.55      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u258,axiom,
% 0.21/0.55      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u257,negated_conjecture,
% 0.21/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.55  
% 0.21/0.55  % (2766)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  tff(u256,negated_conjecture,
% 0.21/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u255,negated_conjecture,
% 0.21/0.55      (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u254,negated_conjecture,
% 0.21/0.55      (k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u253,axiom,
% 0.21/0.55      (![X3, X4] : (((k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X4)) | (k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3)) | (k1_zfmisc_1(X3) = k1_zfmisc_1(X4)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u252,axiom,
% 0.21/0.55      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u251,negated_conjecture,
% 0.21/0.55      (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  tff(u250,negated_conjecture,
% 0.21/0.55      (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u249,negated_conjecture,
% 0.21/0.55      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u248,axiom,
% 0.21/0.55      (![X0] : ((k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u247,negated_conjecture,
% 0.21/0.55      (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u246,negated_conjecture,
% 0.21/0.55      (sK1 = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u245,axiom,
% 0.21/0.55      (![X1, X0] : (((sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1))) | (k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0)) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u244,axiom,
% 0.21/0.55      (![X1, X0] : (((sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0))) | (k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1)) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u243,axiom,
% 0.21/0.55      (![X1, X2] : (((sK2(X1,k1_zfmisc_1(X2)) = k1_setfam_1(k2_enumset1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X2))) | (sK2(X1,k1_zfmisc_1(X2)) = k1_setfam_1(k2_enumset1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(X2)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u242,axiom,
% 0.21/0.55      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u241,axiom,
% 0.21/0.55      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u240,axiom,
% 0.21/0.55      (![X3, X2] : ((~r1_tarski(X2,sK2(X2,X3)) | (k1_zfmisc_1(X2) = X3) | (sK2(X2,X3) = X2) | r2_hidden(sK2(X2,X3),X3))))).
% 0.21/0.55  
% 0.21/0.55  tff(u239,axiom,
% 0.21/0.55      (![X3, X4] : ((~r1_tarski(X3,sK2(X3,k1_zfmisc_1(X4))) | (sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X4))) | (sK2(X3,k1_zfmisc_1(X4)) = X3) | (k1_zfmisc_1(X3) = k1_zfmisc_1(X4)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u238,axiom,
% 0.21/0.55      (![X3, X2] : ((~r1_tarski(X2,sK2(X2,k1_zfmisc_1(X3))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | (sK2(X2,k1_zfmisc_1(X3)) = X2) | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3))))).
% 0.21/0.55  
% 0.21/0.55  tff(u237,axiom,
% 0.21/0.55      (![X5, X4] : ((~r1_tarski(X5,sK2(X4,k1_zfmisc_1(X5))) | (sK2(X4,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(sK2(X4,k1_zfmisc_1(X5)),sK2(X4,k1_zfmisc_1(X5)),sK2(X4,k1_zfmisc_1(X5)),X4))) | (sK2(X4,k1_zfmisc_1(X5)) = X5) | (k1_zfmisc_1(X4) = k1_zfmisc_1(X5)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u236,axiom,
% 0.21/0.55      (![X3, X2] : ((~r1_tarski(X3,sK2(X2,k1_zfmisc_1(X3))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | (sK2(X2,k1_zfmisc_1(X3)) = X3) | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2))))).
% 0.21/0.55  
% 0.21/0.55  tff(u235,negated_conjecture,
% 0.21/0.55      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  tff(u234,negated_conjecture,
% 0.21/0.55      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  tff(u233,axiom,
% 0.21/0.55      (![X1, X0] : ((~r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)) | ~r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u232,axiom,
% 0.21/0.55      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u231,negated_conjecture,
% 0.21/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  tff(u230,axiom,
% 0.21/0.55      (![X1, X0] : ((r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)) | (sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1))))))).
% 0.21/0.55  
% 0.21/0.55  tff(u229,axiom,
% 0.21/0.55      (![X1, X0] : ((r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)) | (sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X0))))))).
% 0.21/0.55  
% 0.21/0.55  tff(u228,axiom,
% 0.21/0.55      (![X1, X0] : ((r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u227,axiom,
% 0.21/0.55      (![X3, X0] : ((~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u226,axiom,
% 0.21/0.55      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | ~r1_tarski(sK2(X0,X1),X0) | (k1_zfmisc_1(X0) = X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u225,axiom,
% 0.21/0.55      (![X3, X0] : ((r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u224,axiom,
% 0.21/0.55      (![X0] : (r2_hidden(X0,k1_zfmisc_1(X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u223,negated_conjecture,
% 0.21/0.55      r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u222,axiom,
% 0.21/0.55      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X1) | (k1_zfmisc_1(X0) = X1) | (sK2(X0,X1) = k1_setfam_1(k2_enumset1(sK2(X0,X1),sK2(X0,X1),sK2(X0,X1),X0))))))).
% 0.21/0.55  
% 0.21/0.55  tff(u221,axiom,
% 0.21/0.55      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X1) | r1_tarski(sK2(X0,X1),X0) | (k1_zfmisc_1(X0) = X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u220,axiom,
% 0.21/0.55      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u219,axiom,
% 0.21/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u218,axiom,
% 0.21/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u217,axiom,
% 0.21/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u216,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u215,axiom,
% 0.21/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u214,axiom,
% 0.21/0.55      (![X0] : (~v1_xboole_0(k1_zfmisc_1(X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u213,negated_conjecture,
% 0.21/0.55      l1_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  % (2756)# SZS output end Saturation.
% 0.21/0.55  % (2756)------------------------------
% 0.21/0.55  % (2756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2756)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (2756)Memory used [KB]: 10874
% 0.21/0.55  % (2756)Time elapsed: 0.119 s
% 0.21/0.55  % (2756)------------------------------
% 0.21/0.55  % (2756)------------------------------
% 0.21/0.55  % (2749)Success in time 0.181 s
%------------------------------------------------------------------------------
