%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 1.35s
% Output     : Saturation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   54 (  54 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u288,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u287,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 )).

tff(u286,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u285,axiom,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) )).

tff(u284,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )).

tff(u283,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u282,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u281,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u280,axiom,(
    ! [X5] : k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0) )).

tff(u279,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u278,axiom,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 )).

tff(u277,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u276,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) )).

tff(u275,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u274,axiom,(
    ! [X3,X4] : k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4) )).

tff(u273,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u272,axiom,(
    ! [X3,X4] : k7_subset_1(X3,k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) )).

tff(u271,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u270,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u269,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u268,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u267,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u266,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u265,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u264,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u263,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u262,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u261,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u260,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u259,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u258,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u257,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u256,axiom,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)) ) )).

tff(u255,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11034)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (11033)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (11034)Refutation not found, incomplete strategy% (11034)------------------------------
% 0.22/0.51  % (11034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11050)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (11023)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (11034)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11034)Memory used [KB]: 6268
% 0.22/0.52  % (11034)Time elapsed: 0.098 s
% 0.22/0.52  % (11034)------------------------------
% 0.22/0.52  % (11034)------------------------------
% 0.22/0.52  % (11022)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (11042)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (11026)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11033)Refutation not found, incomplete strategy% (11033)------------------------------
% 0.22/0.52  % (11033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11033)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11033)Memory used [KB]: 10618
% 0.22/0.52  % (11033)Time elapsed: 0.118 s
% 0.22/0.52  % (11033)------------------------------
% 0.22/0.52  % (11033)------------------------------
% 0.22/0.52  % (11035)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (11042)Refutation not found, incomplete strategy% (11042)------------------------------
% 0.22/0.52  % (11042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11042)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11042)Memory used [KB]: 10746
% 0.22/0.53  % (11042)Time elapsed: 0.109 s
% 0.22/0.53  % (11042)------------------------------
% 0.22/0.53  % (11042)------------------------------
% 0.22/0.53  % (11049)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (11031)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (11025)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (11047)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (11041)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (11047)Refutation not found, incomplete strategy% (11047)------------------------------
% 0.22/0.54  % (11047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11047)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11047)Memory used [KB]: 6268
% 0.22/0.54  % (11047)Time elapsed: 0.131 s
% 0.22/0.54  % (11047)------------------------------
% 0.22/0.54  % (11047)------------------------------
% 0.22/0.54  % (11025)Refutation not found, incomplete strategy% (11025)------------------------------
% 0.22/0.54  % (11025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11025)Memory used [KB]: 10746
% 0.22/0.54  % (11025)Time elapsed: 0.130 s
% 0.22/0.54  % (11025)------------------------------
% 0.22/0.54  % (11025)------------------------------
% 0.22/0.54  % (11043)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (11026)Refutation not found, incomplete strategy% (11026)------------------------------
% 0.22/0.54  % (11026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11026)Memory used [KB]: 6140
% 0.22/0.54  % (11026)Time elapsed: 0.130 s
% 0.22/0.54  % (11026)------------------------------
% 0.22/0.54  % (11026)------------------------------
% 0.22/0.54  % (11023)Refutation not found, incomplete strategy% (11023)------------------------------
% 0.22/0.54  % (11023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11023)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11023)Memory used [KB]: 10746
% 0.22/0.54  % (11023)Time elapsed: 0.127 s
% 0.22/0.54  % (11023)------------------------------
% 0.22/0.54  % (11023)------------------------------
% 0.22/0.54  % (11046)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (11030)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (11048)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (11039)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (11032)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (11048)Refutation not found, incomplete strategy% (11048)------------------------------
% 0.22/0.55  % (11048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11048)Memory used [KB]: 10746
% 0.22/0.55  % (11048)Time elapsed: 0.142 s
% 0.22/0.55  % (11048)------------------------------
% 0.22/0.55  % (11048)------------------------------
% 1.35/0.55  % (11027)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.55  % (11038)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.55  % (11040)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (11027)Refutation not found, incomplete strategy% (11027)------------------------------
% 1.35/0.55  % (11027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11027)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (11027)Memory used [KB]: 6268
% 1.35/0.55  % (11027)Time elapsed: 0.139 s
% 1.35/0.55  % (11027)------------------------------
% 1.35/0.55  % (11027)------------------------------
% 1.35/0.55  % (11021)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.55  % (11021)Refutation not found, incomplete strategy% (11021)------------------------------
% 1.35/0.55  % (11021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11021)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (11021)Memory used [KB]: 1663
% 1.35/0.55  % (11021)Time elapsed: 0.134 s
% 1.35/0.55  % (11021)------------------------------
% 1.35/0.55  % (11021)------------------------------
% 1.35/0.55  % (11039)Refutation not found, incomplete strategy% (11039)------------------------------
% 1.35/0.55  % (11039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11039)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (11039)Memory used [KB]: 10618
% 1.35/0.55  % (11039)Time elapsed: 0.140 s
% 1.35/0.55  % (11039)------------------------------
% 1.35/0.55  % (11039)------------------------------
% 1.35/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.35/0.55  % (11038)# SZS output start Saturation.
% 1.35/0.55  tff(u288,negated_conjecture,
% 1.35/0.55      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u287,axiom,
% 1.35/0.55      (![X0] : ((k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u286,axiom,
% 1.35/0.55      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 1.35/0.55  
% 1.35/0.55  tff(u285,axiom,
% 1.35/0.55      (![X1] : ((k1_xboole_0 = k3_subset_1(X1,X1))))).
% 1.35/0.55  
% 1.35/0.55  tff(u284,axiom,
% 1.35/0.55      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))).
% 1.35/0.55  
% 1.35/0.55  tff(u283,negated_conjecture,
% 1.35/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.35/0.55  
% 1.35/0.55  tff(u282,negated_conjecture,
% 1.35/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.35/0.55  
% 1.35/0.55  tff(u281,axiom,
% 1.35/0.55      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 1.35/0.55  
% 1.35/0.55  tff(u280,axiom,
% 1.35/0.55      (![X5] : ((k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0))))).
% 1.35/0.55  
% 1.35/0.55  tff(u279,axiom,
% 1.35/0.55      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u278,axiom,
% 1.35/0.55      (![X1] : ((k3_subset_1(X1,k1_xboole_0) = X1)))).
% 1.35/0.55  
% 1.35/0.55  tff(u277,negated_conjecture,
% 1.35/0.55      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 1.35/0.55  
% 1.35/0.55  tff(u276,negated_conjecture,
% 1.35/0.55      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u275,axiom,
% 1.35/0.55      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u274,axiom,
% 1.35/0.55      (![X3, X4] : ((k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4))))).
% 1.35/0.55  
% 1.35/0.55  tff(u273,axiom,
% 1.35/0.55      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 1.35/0.55  
% 1.35/0.55  tff(u272,axiom,
% 1.35/0.55      (![X3, X4] : ((k7_subset_1(X3,k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))))))).
% 1.35/0.55  
% 1.35/0.55  tff(u271,negated_conjecture,
% 1.35/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u270,negated_conjecture,
% 1.35/0.55      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u269,negated_conjecture,
% 1.35/0.55      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 1.35/0.55  
% 1.35/0.55  tff(u268,negated_conjecture,
% 1.35/0.55      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u267,negated_conjecture,
% 1.35/0.55      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u266,axiom,
% 1.35/0.55      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u265,axiom,
% 1.35/0.55      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 1.35/0.55  
% 1.35/0.55  tff(u264,axiom,
% 1.35/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u263,axiom,
% 1.35/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 1.35/0.55  
% 1.35/0.55  tff(u262,axiom,
% 1.35/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 1.35/0.55  
% 1.35/0.55  tff(u261,axiom,
% 1.35/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 1.35/0.55  
% 1.35/0.55  tff(u260,negated_conjecture,
% 1.35/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.35/0.55  
% 1.35/0.55  tff(u259,axiom,
% 1.35/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.35/0.55  
% 1.35/0.55  tff(u258,axiom,
% 1.35/0.55      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 1.35/0.55  
% 1.35/0.55  tff(u257,axiom,
% 1.35/0.55      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 1.35/0.55  
% 1.35/0.55  tff(u256,axiom,
% 1.35/0.55      (![X1] : ((~l1_struct_0(X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0))))))).
% 1.35/0.55  
% 1.35/0.55  tff(u255,negated_conjecture,
% 1.35/0.55      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 1.35/0.55  
% 1.35/0.55  % (11038)# SZS output end Saturation.
% 1.35/0.55  % (11038)------------------------------
% 1.35/0.55  % (11038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11038)Termination reason: Satisfiable
% 1.35/0.55  
% 1.35/0.55  % (11038)Memory used [KB]: 10874
% 1.35/0.55  % (11038)Time elapsed: 0.144 s
% 1.35/0.55  % (11038)------------------------------
% 1.35/0.55  % (11038)------------------------------
% 1.35/0.55  % (11037)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (11019)Success in time 0.182 s
%------------------------------------------------------------------------------
