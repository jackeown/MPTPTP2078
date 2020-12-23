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
% DateTime   : Thu Dec  3 12:45:32 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  89 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 190 expanded)
%              Number of equality atoms :   25 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f72,f71,f119,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f119,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f44,f118])).

fof(f118,plain,(
    ! [X4,X5] :
      ( m1_subset_1(X4,k1_zfmisc_1(X5))
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f105,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f32,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

% (23426)Refutation not found, incomplete strategy% (23426)------------------------------
% (23426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23426)Termination reason: Refutation not found, incomplete strategy

% (23426)Memory used [KB]: 10618
% (23426)Time elapsed: 0.112 s
% (23426)------------------------------
% (23426)------------------------------
fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f105,plain,(
    ! [X8,X9] : m1_subset_1(k6_subset_1(X9,k6_subset_1(X9,X8)),k1_zfmisc_1(X8)) ),
    inference(superposition,[],[f27,f45])).

fof(f45,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f42,f42])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f44,plain,(
    ~ m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f22,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f71,plain,(
    r2_hidden(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f20,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (23422)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f23,f36])).

fof(f23,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:30:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1217822720)
% 0.21/0.37  ipcrm: permission denied for id (1217888258)
% 0.21/0.37  ipcrm: permission denied for id (1222082564)
% 0.21/0.38  ipcrm: permission denied for id (1222115333)
% 0.21/0.38  ipcrm: permission denied for id (1217986566)
% 0.21/0.38  ipcrm: permission denied for id (1218019335)
% 0.21/0.38  ipcrm: permission denied for id (1222246411)
% 0.21/0.38  ipcrm: permission denied for id (1222279180)
% 0.21/0.39  ipcrm: permission denied for id (1218150413)
% 0.21/0.39  ipcrm: permission denied for id (1218183182)
% 0.21/0.39  ipcrm: permission denied for id (1222311951)
% 0.21/0.39  ipcrm: permission denied for id (1218248720)
% 0.21/0.39  ipcrm: permission denied for id (1218281489)
% 0.21/0.39  ipcrm: permission denied for id (1222344722)
% 0.21/0.39  ipcrm: permission denied for id (1218347027)
% 0.21/0.39  ipcrm: permission denied for id (1222377492)
% 0.21/0.40  ipcrm: permission denied for id (1218445334)
% 0.21/0.40  ipcrm: permission denied for id (1218478103)
% 0.21/0.40  ipcrm: permission denied for id (1218510872)
% 0.21/0.40  ipcrm: permission denied for id (1222443033)
% 0.21/0.40  ipcrm: permission denied for id (1218576410)
% 0.21/0.40  ipcrm: permission denied for id (1218609179)
% 0.21/0.40  ipcrm: permission denied for id (1218641948)
% 0.21/0.41  ipcrm: permission denied for id (1218674717)
% 0.21/0.41  ipcrm: permission denied for id (1222541344)
% 0.21/0.41  ipcrm: permission denied for id (1222606882)
% 0.21/0.41  ipcrm: permission denied for id (1218871331)
% 0.21/0.41  ipcrm: permission denied for id (1222639652)
% 0.21/0.42  ipcrm: permission denied for id (1218969638)
% 0.21/0.42  ipcrm: permission denied for id (1222705191)
% 0.21/0.42  ipcrm: permission denied for id (1219067944)
% 0.21/0.42  ipcrm: permission denied for id (1219100713)
% 0.21/0.42  ipcrm: permission denied for id (1222737962)
% 0.21/0.42  ipcrm: permission denied for id (1219231788)
% 0.21/0.43  ipcrm: permission denied for id (1219264557)
% 0.21/0.43  ipcrm: permission denied for id (1219395633)
% 0.21/0.43  ipcrm: permission denied for id (1219428402)
% 0.21/0.43  ipcrm: permission denied for id (1222934579)
% 0.21/0.44  ipcrm: permission denied for id (1222967348)
% 0.21/0.44  ipcrm: permission denied for id (1223000117)
% 0.22/0.44  ipcrm: permission denied for id (1223065655)
% 0.22/0.44  ipcrm: permission denied for id (1223098424)
% 0.22/0.44  ipcrm: permission denied for id (1223131193)
% 0.22/0.44  ipcrm: permission denied for id (1219690554)
% 0.22/0.45  ipcrm: permission denied for id (1219723323)
% 0.22/0.45  ipcrm: permission denied for id (1219756092)
% 0.22/0.45  ipcrm: permission denied for id (1223163965)
% 0.22/0.45  ipcrm: permission denied for id (1219887168)
% 0.22/0.46  ipcrm: permission denied for id (1219952705)
% 0.22/0.46  ipcrm: permission denied for id (1223262274)
% 0.22/0.46  ipcrm: permission denied for id (1223295043)
% 0.22/0.46  ipcrm: permission denied for id (1220051012)
% 0.22/0.46  ipcrm: permission denied for id (1220116550)
% 0.22/0.47  ipcrm: permission denied for id (1220182088)
% 0.22/0.47  ipcrm: permission denied for id (1220214857)
% 0.22/0.47  ipcrm: permission denied for id (1220313164)
% 0.22/0.48  ipcrm: permission denied for id (1223491662)
% 0.22/0.48  ipcrm: permission denied for id (1220411471)
% 0.22/0.48  ipcrm: permission denied for id (1223524432)
% 0.22/0.48  ipcrm: permission denied for id (1220509778)
% 0.22/0.48  ipcrm: permission denied for id (1220542547)
% 0.22/0.48  ipcrm: permission denied for id (1223589972)
% 0.22/0.49  ipcrm: permission denied for id (1220608085)
% 0.22/0.49  ipcrm: permission denied for id (1220640854)
% 0.22/0.49  ipcrm: permission denied for id (1223622743)
% 0.22/0.49  ipcrm: permission denied for id (1220771930)
% 0.22/0.49  ipcrm: permission denied for id (1220804699)
% 0.22/0.49  ipcrm: permission denied for id (1220837468)
% 0.22/0.50  ipcrm: permission denied for id (1220903006)
% 0.22/0.50  ipcrm: permission denied for id (1223753823)
% 0.22/0.50  ipcrm: permission denied for id (1220968544)
% 0.22/0.50  ipcrm: permission denied for id (1221001313)
% 0.22/0.50  ipcrm: permission denied for id (1221066851)
% 0.22/0.50  ipcrm: permission denied for id (1221165158)
% 0.22/0.50  ipcrm: permission denied for id (1221197927)
% 0.22/0.50  ipcrm: permission denied for id (1221230696)
% 0.22/0.51  ipcrm: permission denied for id (1221263465)
% 0.22/0.51  ipcrm: permission denied for id (1223884906)
% 0.22/0.51  ipcrm: permission denied for id (1221361772)
% 0.22/0.51  ipcrm: permission denied for id (1221394541)
% 0.22/0.51  ipcrm: permission denied for id (1223950446)
% 0.22/0.51  ipcrm: permission denied for id (1223983215)
% 0.22/0.51  ipcrm: permission denied for id (1221492849)
% 0.22/0.52  ipcrm: permission denied for id (1221591156)
% 0.22/0.52  ipcrm: permission denied for id (1221623925)
% 0.22/0.52  ipcrm: permission denied for id (1224114294)
% 0.22/0.52  ipcrm: permission denied for id (1221722232)
% 0.22/0.52  ipcrm: permission denied for id (1224212601)
% 0.22/0.52  ipcrm: permission denied for id (1224310908)
% 0.22/0.52  ipcrm: permission denied for id (1224343677)
% 0.22/0.52  ipcrm: permission denied for id (1224376446)
% 0.22/0.53  ipcrm: permission denied for id (1221984383)
% 1.15/0.66  % (23436)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.15/0.67  % (23423)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.15/0.67  % (23424)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.15/0.67  % (23429)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.15/0.67  % (23417)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.15/0.67  % (23444)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.15/0.67  % (23418)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.15/0.67  % (23436)Refutation not found, incomplete strategy% (23436)------------------------------
% 1.15/0.67  % (23436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (23445)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.15/0.67  % (23436)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.67  
% 1.15/0.67  % (23436)Memory used [KB]: 10746
% 1.15/0.67  % (23436)Time elapsed: 0.093 s
% 1.15/0.67  % (23436)------------------------------
% 1.15/0.67  % (23436)------------------------------
% 1.15/0.68  % (23428)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.15/0.68  % (23424)Refutation not found, incomplete strategy% (23424)------------------------------
% 1.15/0.68  % (23424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.68  % (23434)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.15/0.68  % (23440)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.15/0.68  % (23424)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.68  
% 1.15/0.68  % (23424)Memory used [KB]: 10618
% 1.15/0.68  % (23424)Time elapsed: 0.113 s
% 1.15/0.68  % (23424)------------------------------
% 1.15/0.68  % (23424)------------------------------
% 1.15/0.68  % (23431)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.15/0.68  % (23426)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.15/0.68  % (23425)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.15/0.69  % (23438)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.15/0.69  % (23438)Refutation not found, incomplete strategy% (23438)------------------------------
% 1.15/0.69  % (23438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (23438)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.69  
% 1.15/0.69  % (23438)Memory used [KB]: 10746
% 1.15/0.69  % (23438)Time elapsed: 0.103 s
% 1.15/0.69  % (23438)------------------------------
% 1.15/0.69  % (23438)------------------------------
% 1.15/0.69  % (23431)Refutation not found, incomplete strategy% (23431)------------------------------
% 1.15/0.69  % (23431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (23431)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.69  
% 1.15/0.69  % (23431)Memory used [KB]: 6268
% 1.15/0.69  % (23431)Time elapsed: 0.108 s
% 1.15/0.69  % (23431)------------------------------
% 1.15/0.69  % (23431)------------------------------
% 1.15/0.69  % (23440)Refutation found. Thanks to Tanya!
% 1.15/0.69  % SZS status Theorem for theBenchmark
% 1.15/0.69  % SZS output start Proof for theBenchmark
% 1.15/0.69  fof(f165,plain,(
% 1.15/0.69    $false),
% 1.15/0.69    inference(unit_resulting_resolution,[],[f72,f71,f119,f48])).
% 1.15/0.69  fof(f48,plain,(
% 1.15/0.69    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.15/0.69    inference(definition_unfolding,[],[f41,f43])).
% 1.15/0.69  fof(f43,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.15/0.69    inference(definition_unfolding,[],[f30,f38])).
% 1.15/0.69  fof(f38,plain,(
% 1.15/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f8])).
% 1.15/0.69  fof(f8,axiom,(
% 1.15/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.15/0.69  fof(f30,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f7])).
% 1.15/0.69  fof(f7,axiom,(
% 1.15/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.15/0.69  fof(f41,plain,(
% 1.15/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f9])).
% 1.15/0.69  fof(f9,axiom,(
% 1.15/0.69    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.15/0.69  fof(f119,plain,(
% 1.15/0.69    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),sK0)),
% 1.15/0.69    inference(unit_resulting_resolution,[],[f44,f118])).
% 1.15/0.69  fof(f118,plain,(
% 1.15/0.69    ( ! [X4,X5] : (m1_subset_1(X4,k1_zfmisc_1(X5)) | ~r1_tarski(X4,X5)) )),
% 1.15/0.69    inference(superposition,[],[f105,f47])).
% 1.15/0.69  fof(f47,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.15/0.69    inference(definition_unfolding,[],[f37,f42])).
% 1.15/0.69  fof(f42,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.15/0.69    inference(definition_unfolding,[],[f32,f28,f28])).
% 1.15/0.69  fof(f28,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f12])).
% 1.15/0.69  fof(f12,axiom,(
% 1.15/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.15/0.69  fof(f32,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.15/0.69    inference(cnf_transformation,[],[f6])).
% 1.15/0.69  fof(f6,axiom,(
% 1.15/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.15/0.69  fof(f37,plain,(
% 1.15/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.15/0.69    inference(cnf_transformation,[],[f19])).
% 1.15/0.69  % (23426)Refutation not found, incomplete strategy% (23426)------------------------------
% 1.15/0.69  % (23426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (23426)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.69  
% 1.15/0.69  % (23426)Memory used [KB]: 10618
% 1.15/0.69  % (23426)Time elapsed: 0.112 s
% 1.15/0.69  % (23426)------------------------------
% 1.15/0.69  % (23426)------------------------------
% 1.15/0.69  fof(f19,plain,(
% 1.15/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.15/0.69    inference(ennf_transformation,[],[f5])).
% 1.15/0.69  fof(f5,axiom,(
% 1.15/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.15/0.69  fof(f105,plain,(
% 1.15/0.69    ( ! [X8,X9] : (m1_subset_1(k6_subset_1(X9,k6_subset_1(X9,X8)),k1_zfmisc_1(X8))) )),
% 1.15/0.69    inference(superposition,[],[f27,f45])).
% 1.15/0.69  fof(f45,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 1.15/0.69    inference(definition_unfolding,[],[f29,f42,f42])).
% 1.15/0.69  fof(f29,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f1])).
% 1.15/0.69  fof(f1,axiom,(
% 1.15/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.15/0.69  fof(f27,plain,(
% 1.15/0.69    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.15/0.69    inference(cnf_transformation,[],[f11])).
% 1.15/0.69  fof(f11,axiom,(
% 1.15/0.69    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.15/0.69  fof(f44,plain,(
% 1.15/0.69    ~m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.15/0.69    inference(definition_unfolding,[],[f22,f43])).
% 1.15/0.69  fof(f22,plain,(
% 1.15/0.69    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.15/0.69    inference(cnf_transformation,[],[f16])).
% 1.15/0.69  fof(f16,plain,(
% 1.15/0.69    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.15/0.69    inference(flattening,[],[f15])).
% 1.15/0.69  fof(f15,plain,(
% 1.15/0.69    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.15/0.69    inference(ennf_transformation,[],[f14])).
% 1.15/0.69  fof(f14,negated_conjecture,(
% 1.15/0.69    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 1.15/0.69    inference(negated_conjecture,[],[f13])).
% 1.15/0.69  fof(f13,conjecture,(
% 1.15/0.69    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).
% 1.15/0.69  fof(f71,plain,(
% 1.15/0.69    r2_hidden(sK2,sK0)),
% 1.15/0.69    inference(unit_resulting_resolution,[],[f52,f20,f36])).
% 1.15/0.69  fof(f36,plain,(
% 1.15/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f18])).
% 1.15/0.69  % (23422)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.15/0.69  fof(f18,plain,(
% 1.15/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.15/0.69    inference(ennf_transformation,[],[f10])).
% 1.15/0.69  fof(f10,axiom,(
% 1.15/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.15/0.69  fof(f20,plain,(
% 1.15/0.69    m1_subset_1(sK2,sK0)),
% 1.15/0.69    inference(cnf_transformation,[],[f16])).
% 1.15/0.69  fof(f52,plain,(
% 1.15/0.69    ~v1_xboole_0(sK0)),
% 1.15/0.69    inference(unit_resulting_resolution,[],[f21,f24])).
% 1.15/0.69  fof(f24,plain,(
% 1.15/0.69    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f17])).
% 1.15/0.69  fof(f17,plain,(
% 1.15/0.69    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.15/0.69    inference(ennf_transformation,[],[f3])).
% 1.15/0.69  fof(f3,axiom,(
% 1.15/0.69    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.15/0.69  fof(f21,plain,(
% 1.15/0.69    k1_xboole_0 != sK0),
% 1.15/0.69    inference(cnf_transformation,[],[f16])).
% 1.15/0.69  fof(f72,plain,(
% 1.15/0.69    r2_hidden(sK1,sK0)),
% 1.15/0.69    inference(unit_resulting_resolution,[],[f52,f23,f36])).
% 1.15/0.69  fof(f23,plain,(
% 1.15/0.69    m1_subset_1(sK1,sK0)),
% 1.15/0.69    inference(cnf_transformation,[],[f16])).
% 1.15/0.69  % SZS output end Proof for theBenchmark
% 1.15/0.69  % (23440)------------------------------
% 1.15/0.69  % (23440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (23440)Termination reason: Refutation
% 1.15/0.69  
% 1.15/0.69  % (23440)Memory used [KB]: 6268
% 1.15/0.69  % (23440)Time elapsed: 0.122 s
% 1.15/0.69  % (23440)------------------------------
% 1.15/0.69  % (23440)------------------------------
% 1.15/0.69  % (23419)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.15/0.69  % (23250)Success in time 0.323 s
%------------------------------------------------------------------------------
