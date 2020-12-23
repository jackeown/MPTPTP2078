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
% DateTime   : Thu Dec  3 12:47:25 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 147 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 295 expanded)
%              Number of equality atoms :   10 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f188,f191,f233])).

fof(f233,plain,
    ( spl3_2
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f22,f19,f163,f51,f135,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f135,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_2
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2) ),
    inference(superposition,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f25,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f163,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_8
  <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f21,f22,f46,f131,f163,f23])).

fof(f131,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f188,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f19,f51,f164,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f164,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f136,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f125,f133,f129])).

fof(f125,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f36,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f20,f35,f35])).

fof(f20,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:05:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (24868)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.49  % (24884)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.49  % (24884)Refutation not found, incomplete strategy% (24884)------------------------------
% 0.21/0.49  % (24884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24884)Memory used [KB]: 10746
% 0.21/0.49  % (24884)Time elapsed: 0.072 s
% 0.21/0.49  % (24884)------------------------------
% 0.21/0.49  % (24884)------------------------------
% 0.21/0.52  % (24858)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (24873)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (24869)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (24870)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (24867)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (24870)Refutation not found, incomplete strategy% (24870)------------------------------
% 0.21/0.56  % (24870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24870)Memory used [KB]: 1663
% 0.21/0.56  % (24870)Time elapsed: 0.090 s
% 0.21/0.56  % (24870)------------------------------
% 0.21/0.56  % (24870)------------------------------
% 0.21/0.56  % (24857)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (24857)Refutation not found, incomplete strategy% (24857)------------------------------
% 0.21/0.56  % (24857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24857)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24857)Memory used [KB]: 1663
% 0.21/0.56  % (24857)Time elapsed: 0.153 s
% 0.21/0.56  % (24857)------------------------------
% 0.21/0.56  % (24857)------------------------------
% 0.21/0.57  % (24864)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.57  % (24876)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.58  % (24877)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.58  % (24860)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.58  % (24878)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.58  % (24856)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.58  % (24869)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % SZS output start Proof for theBenchmark
% 1.42/0.58  fof(f234,plain,(
% 1.42/0.58    $false),
% 1.42/0.58    inference(avatar_sat_refutation,[],[f136,f188,f191,f233])).
% 1.42/0.58  fof(f233,plain,(
% 1.42/0.58    spl3_2 | ~spl3_8),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f230])).
% 1.42/0.58  fof(f230,plain,(
% 1.42/0.58    $false | (spl3_2 | ~spl3_8)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f22,f19,f163,f51,f135,f23])).
% 1.42/0.58  fof(f23,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f14])).
% 1.42/0.58  fof(f14,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(flattening,[],[f13])).
% 1.42/0.58  fof(f13,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(ennf_transformation,[],[f9])).
% 1.42/0.58  fof(f9,axiom,(
% 1.42/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.42/0.58  fof(f135,plain,(
% 1.42/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl3_2),
% 1.42/0.58    inference(avatar_component_clause,[],[f133])).
% 1.42/0.58  fof(f133,plain,(
% 1.42/0.58    spl3_2 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.42/0.58  fof(f51,plain,(
% 1.42/0.58    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2)) )),
% 1.42/0.58    inference(superposition,[],[f46,f37])).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.42/0.58    inference(definition_unfolding,[],[f25,f35,f35])).
% 1.42/0.58  fof(f35,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.42/0.58    inference(definition_unfolding,[],[f26,f27])).
% 1.42/0.58  fof(f27,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f6])).
% 1.42/0.58  fof(f6,axiom,(
% 1.42/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.58  fof(f25,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f1])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.42/0.58  fof(f46,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.42/0.58    inference(resolution,[],[f38,f40])).
% 1.42/0.58  fof(f40,plain,(
% 1.42/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.58    inference(equality_resolution,[],[f29])).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f2])).
% 1.42/0.58  fof(f2,axiom,(
% 1.42/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.58  fof(f38,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(definition_unfolding,[],[f33,f35])).
% 1.42/0.58  fof(f33,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f16])).
% 1.42/0.58  fof(f16,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.42/0.58    inference(ennf_transformation,[],[f3])).
% 1.42/0.58  fof(f3,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.42/0.58  fof(f163,plain,(
% 1.42/0.58    v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~spl3_8),
% 1.42/0.58    inference(avatar_component_clause,[],[f162])).
% 1.42/0.58  fof(f162,plain,(
% 1.42/0.58    spl3_8 <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.42/0.58  fof(f19,plain,(
% 1.42/0.58    v1_relat_1(sK2)),
% 1.42/0.58    inference(cnf_transformation,[],[f12])).
% 1.42/0.58  fof(f12,plain,(
% 1.42/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.42/0.58    inference(ennf_transformation,[],[f11])).
% 1.42/0.58  fof(f11,negated_conjecture,(
% 1.42/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.42/0.58    inference(negated_conjecture,[],[f10])).
% 1.42/0.58  fof(f10,conjecture,(
% 1.42/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 1.42/0.58  fof(f22,plain,(
% 1.42/0.58    v1_relat_1(sK0)),
% 1.42/0.58    inference(cnf_transformation,[],[f12])).
% 1.42/0.58  fof(f191,plain,(
% 1.42/0.58    spl3_1 | ~spl3_8),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f189])).
% 1.42/0.58  fof(f189,plain,(
% 1.42/0.58    $false | (spl3_1 | ~spl3_8)),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f21,f22,f46,f131,f163,f23])).
% 1.42/0.58  fof(f131,plain,(
% 1.42/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl3_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f129])).
% 1.42/0.58  fof(f129,plain,(
% 1.42/0.58    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.42/0.58  fof(f21,plain,(
% 1.42/0.58    v1_relat_1(sK1)),
% 1.42/0.58    inference(cnf_transformation,[],[f12])).
% 1.42/0.58  fof(f188,plain,(
% 1.42/0.58    spl3_8),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f181])).
% 1.42/0.58  fof(f181,plain,(
% 1.42/0.58    $false | spl3_8),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f19,f51,f164,f43])).
% 1.42/0.58  fof(f43,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.58    inference(resolution,[],[f24,f31])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.58  fof(f24,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f15])).
% 1.42/0.58  fof(f15,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(ennf_transformation,[],[f8])).
% 1.42/0.58  fof(f8,axiom,(
% 1.42/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.42/0.58  fof(f164,plain,(
% 1.42/0.58    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | spl3_8),
% 1.42/0.58    inference(avatar_component_clause,[],[f162])).
% 1.42/0.58  fof(f136,plain,(
% 1.42/0.58    ~spl3_1 | ~spl3_2),
% 1.42/0.58    inference(avatar_split_clause,[],[f125,f133,f129])).
% 1.42/0.58  fof(f125,plain,(
% 1.42/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.42/0.58    inference(resolution,[],[f36,f39])).
% 1.42/0.58  fof(f39,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(definition_unfolding,[],[f34,f35])).
% 1.42/0.58  fof(f34,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f18,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.42/0.58    inference(flattening,[],[f17])).
% 1.42/0.58  fof(f17,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.42/0.58    inference(ennf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.42/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.42/0.58  fof(f36,plain,(
% 1.42/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.42/0.58    inference(definition_unfolding,[],[f20,f35,f35])).
% 1.42/0.58  fof(f20,plain,(
% 1.42/0.58    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.42/0.58    inference(cnf_transformation,[],[f12])).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (24869)------------------------------
% 1.42/0.58  % (24869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (24869)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (24869)Memory used [KB]: 6268
% 1.42/0.58  % (24869)Time elapsed: 0.149 s
% 1.42/0.58  % (24869)------------------------------
% 1.42/0.58  % (24869)------------------------------
% 1.42/0.58  % (24855)Success in time 0.214 s
%------------------------------------------------------------------------------
