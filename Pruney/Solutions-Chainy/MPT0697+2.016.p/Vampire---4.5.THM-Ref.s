%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:08 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 108 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 297 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f180,f706])).

fof(f706,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(subsumption_resolution,[],[f691,f294])).

fof(f294,plain,
    ( ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f133,f142])).

fof(f142,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f66,f71,f76,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f133,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f123,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f123,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f66,f71,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f691,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))
    | ~ spl2_1
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f66,f179,f498,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f498,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f89,f210])).

fof(f210,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k6_subset_1(X2,X3),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(superposition,[],[f56,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f89,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f179,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl2_6
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f180,plain,
    ( ~ spl2_6
    | spl2_4 ),
    inference(avatar_split_clause,[],[f111,f79,f177])).

fof(f79,plain,
    ( spl2_4
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f111,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f81,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f77,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:27 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.52  % (28678)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (28679)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (28687)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (28672)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (28678)Refutation not found, incomplete strategy% (28678)------------------------------
% 0.20/0.52  % (28678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28672)Refutation not found, incomplete strategy% (28672)------------------------------
% 0.20/0.53  % (28672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28678)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28678)Memory used [KB]: 10618
% 0.20/0.54  % (28678)Time elapsed: 0.081 s
% 0.20/0.54  % (28678)------------------------------
% 0.20/0.54  % (28678)------------------------------
% 0.20/0.54  % (28672)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28672)Memory used [KB]: 10618
% 0.20/0.54  % (28672)Time elapsed: 0.085 s
% 0.20/0.54  % (28672)------------------------------
% 0.20/0.54  % (28672)------------------------------
% 0.20/0.54  % (28664)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (28688)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (28684)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (28665)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.54/0.56  % (28690)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.54/0.57  % (28680)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.54/0.58  % (28675)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.54/0.58  % (28663)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.58  % (28670)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.73/0.58  % (28689)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.73/0.58  % (28683)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.73/0.59  % (28671)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.59  % (28669)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.73/0.59  % (28668)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.73/0.59  % (28667)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.73/0.59  % (28673)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.73/0.59  % (28693)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.73/0.59  % (28693)Refutation not found, incomplete strategy% (28693)------------------------------
% 1.73/0.59  % (28693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (28693)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (28693)Memory used [KB]: 1663
% 1.73/0.59  % (28693)Time elapsed: 0.172 s
% 1.73/0.59  % (28693)------------------------------
% 1.73/0.59  % (28693)------------------------------
% 1.73/0.60  % (28685)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.60  % (28660)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.73/0.60  % (28677)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.60  % (28676)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.73/0.61  % (28661)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.73/0.62  % (28682)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.62  % (28692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.62  % (28686)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.73/0.62  % (28692)Refutation not found, incomplete strategy% (28692)------------------------------
% 1.73/0.62  % (28692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.62  % (28692)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.62  
% 1.73/0.62  % (28692)Memory used [KB]: 10618
% 1.73/0.62  % (28692)Time elapsed: 0.207 s
% 1.73/0.62  % (28692)------------------------------
% 1.73/0.62  % (28692)------------------------------
% 1.73/0.62  % (28674)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.73/0.62  % (28674)Refutation not found, incomplete strategy% (28674)------------------------------
% 1.73/0.62  % (28674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.63  % (28683)Refutation found. Thanks to Tanya!
% 2.11/0.63  % SZS status Theorem for theBenchmark
% 2.11/0.64  % (28674)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (28674)Memory used [KB]: 10618
% 2.11/0.64  % (28674)Time elapsed: 0.209 s
% 2.11/0.64  % (28674)------------------------------
% 2.11/0.64  % (28674)------------------------------
% 2.11/0.64  % SZS output start Proof for theBenchmark
% 2.11/0.64  fof(f708,plain,(
% 2.11/0.64    $false),
% 2.11/0.64    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f180,f706])).
% 2.11/0.64  fof(f706,plain,(
% 2.11/0.64    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_6),
% 2.11/0.64    inference(avatar_contradiction_clause,[],[f705])).
% 2.11/0.64  fof(f705,plain,(
% 2.11/0.64    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_6)),
% 2.11/0.64    inference(subsumption_resolution,[],[f691,f294])).
% 2.11/0.64  fof(f294,plain,(
% 2.11/0.64    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.11/0.64    inference(superposition,[],[f133,f142])).
% 2.11/0.64  fof(f142,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.11/0.64    inference(unit_resulting_resolution,[],[f66,f71,f76,f57])).
% 2.11/0.64  fof(f57,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f31])).
% 2.11/0.64  fof(f31,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.11/0.64    inference(flattening,[],[f30])).
% 2.11/0.64  fof(f30,plain,(
% 2.11/0.64    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.11/0.64    inference(ennf_transformation,[],[f12])).
% 2.11/0.64  fof(f12,axiom,(
% 2.11/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 2.11/0.64  fof(f76,plain,(
% 2.11/0.64    v2_funct_1(sK1) | ~spl2_3),
% 2.11/0.64    inference(avatar_component_clause,[],[f74])).
% 2.11/0.64  fof(f74,plain,(
% 2.11/0.64    spl2_3 <=> v2_funct_1(sK1)),
% 2.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.11/0.64  fof(f71,plain,(
% 2.11/0.64    v1_funct_1(sK1) | ~spl2_2),
% 2.11/0.64    inference(avatar_component_clause,[],[f69])).
% 2.11/0.64  fof(f69,plain,(
% 2.11/0.64    spl2_2 <=> v1_funct_1(sK1)),
% 2.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.11/0.64  fof(f66,plain,(
% 2.11/0.64    v1_relat_1(sK1) | ~spl2_1),
% 2.11/0.64    inference(avatar_component_clause,[],[f64])).
% 2.11/0.64  fof(f64,plain,(
% 2.11/0.64    spl2_1 <=> v1_relat_1(sK1)),
% 2.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.11/0.64  fof(f133,plain,(
% 2.11/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.11/0.64    inference(unit_resulting_resolution,[],[f123,f59])).
% 2.11/0.64  fof(f59,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.11/0.64    inference(definition_unfolding,[],[f54,f44])).
% 2.11/0.64  fof(f44,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f8])).
% 2.11/0.64  fof(f8,axiom,(
% 2.11/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.11/0.64  fof(f54,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f36])).
% 2.11/0.64  fof(f36,plain,(
% 2.11/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.11/0.64    inference(nnf_transformation,[],[f2])).
% 2.11/0.64  fof(f2,axiom,(
% 2.11/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.11/0.64  fof(f123,plain,(
% 2.11/0.64    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.11/0.64    inference(unit_resulting_resolution,[],[f66,f71,f49])).
% 2.11/0.64  fof(f49,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f27])).
% 2.11/0.64  fof(f27,plain,(
% 2.11/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.11/0.64    inference(flattening,[],[f26])).
% 2.11/0.64  fof(f26,plain,(
% 2.11/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.11/0.64    inference(ennf_transformation,[],[f13])).
% 2.11/0.64  fof(f13,axiom,(
% 2.11/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.26/0.65  fof(f691,plain,(
% 2.26/0.65    k1_xboole_0 != k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)) | (~spl2_1 | spl2_6)),
% 2.26/0.65    inference(unit_resulting_resolution,[],[f66,f179,f498,f47])).
% 2.26/0.65  fof(f47,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f24])).
% 2.26/0.65  fof(f24,plain,(
% 2.26/0.65    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 2.26/0.65    inference(flattening,[],[f23])).
% 2.26/0.65  fof(f23,plain,(
% 2.26/0.65    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f9])).
% 2.26/0.65  fof(f9,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 2.26/0.65  fof(f498,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) ) | ~spl2_1),
% 2.26/0.65    inference(unit_resulting_resolution,[],[f89,f210])).
% 2.26/0.65  fof(f210,plain,(
% 2.26/0.65    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),X4) | ~r1_tarski(X2,X4)) )),
% 2.26/0.65    inference(superposition,[],[f56,f92])).
% 2.26/0.65  fof(f92,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k2_xboole_0(k6_subset_1(X0,X1),X0) = X0) )),
% 2.26/0.65    inference(unit_resulting_resolution,[],[f58,f48])).
% 2.26/0.65  fof(f48,plain,(
% 2.26/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.26/0.65    inference(cnf_transformation,[],[f25])).
% 2.26/0.65  fof(f25,plain,(
% 2.26/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f4])).
% 2.26/0.65  fof(f4,axiom,(
% 2.26/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.26/0.65  fof(f58,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.26/0.65    inference(definition_unfolding,[],[f43,f44])).
% 2.26/0.65  fof(f43,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f6])).
% 2.26/0.65  fof(f6,axiom,(
% 2.26/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.26/0.65  fof(f56,plain,(
% 2.26/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f29])).
% 2.26/0.65  fof(f29,plain,(
% 2.26/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.26/0.65    inference(ennf_transformation,[],[f3])).
% 2.26/0.65  fof(f3,axiom,(
% 2.26/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.26/0.65  fof(f89,plain,(
% 2.26/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_1),
% 2.26/0.65    inference(unit_resulting_resolution,[],[f66,f45])).
% 2.26/0.65  fof(f45,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f20])).
% 2.26/0.65  fof(f20,plain,(
% 2.26/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f10])).
% 2.26/0.65  fof(f10,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.26/0.65  fof(f179,plain,(
% 2.26/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_6),
% 2.26/0.65    inference(avatar_component_clause,[],[f177])).
% 2.26/0.65  fof(f177,plain,(
% 2.26/0.65    spl2_6 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.26/0.65  fof(f180,plain,(
% 2.26/0.65    ~spl2_6 | spl2_4),
% 2.26/0.65    inference(avatar_split_clause,[],[f111,f79,f177])).
% 2.26/0.65  fof(f79,plain,(
% 2.26/0.65    spl2_4 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.26/0.65  fof(f111,plain,(
% 2.26/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_4),
% 2.26/0.65    inference(unit_resulting_resolution,[],[f81,f60])).
% 2.26/0.65  fof(f60,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.26/0.65    inference(definition_unfolding,[],[f53,f44])).
% 2.26/0.65  fof(f53,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.26/0.65    inference(cnf_transformation,[],[f36])).
% 2.26/0.65  fof(f81,plain,(
% 2.26/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_4),
% 2.26/0.65    inference(avatar_component_clause,[],[f79])).
% 2.26/0.65  fof(f82,plain,(
% 2.26/0.65    ~spl2_4),
% 2.26/0.65    inference(avatar_split_clause,[],[f40,f79])).
% 2.26/0.65  fof(f40,plain,(
% 2.26/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.26/0.65    inference(cnf_transformation,[],[f33])).
% 2.26/0.65  fof(f33,plain,(
% 2.26/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.26/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f32])).
% 2.26/0.65  fof(f32,plain,(
% 2.26/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.26/0.65    introduced(choice_axiom,[])).
% 2.26/0.65  fof(f18,plain,(
% 2.26/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.26/0.65    inference(flattening,[],[f17])).
% 2.26/0.65  fof(f17,plain,(
% 2.26/0.65    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.26/0.65    inference(ennf_transformation,[],[f16])).
% 2.26/0.65  fof(f16,negated_conjecture,(
% 2.26/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.26/0.65    inference(negated_conjecture,[],[f15])).
% 2.26/0.65  fof(f15,conjecture,(
% 2.26/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.26/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 2.26/0.65  fof(f77,plain,(
% 2.26/0.65    spl2_3),
% 2.26/0.65    inference(avatar_split_clause,[],[f39,f74])).
% 2.26/0.65  fof(f39,plain,(
% 2.26/0.65    v2_funct_1(sK1)),
% 2.26/0.65    inference(cnf_transformation,[],[f33])).
% 2.26/0.65  fof(f72,plain,(
% 2.26/0.65    spl2_2),
% 2.26/0.65    inference(avatar_split_clause,[],[f38,f69])).
% 2.26/0.65  fof(f38,plain,(
% 2.26/0.65    v1_funct_1(sK1)),
% 2.26/0.65    inference(cnf_transformation,[],[f33])).
% 2.26/0.65  fof(f67,plain,(
% 2.26/0.65    spl2_1),
% 2.26/0.65    inference(avatar_split_clause,[],[f37,f64])).
% 2.26/0.65  fof(f37,plain,(
% 2.26/0.65    v1_relat_1(sK1)),
% 2.26/0.65    inference(cnf_transformation,[],[f33])).
% 2.26/0.65  % SZS output end Proof for theBenchmark
% 2.26/0.65  % (28683)------------------------------
% 2.26/0.65  % (28683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.65  % (28683)Termination reason: Refutation
% 2.26/0.65  
% 2.26/0.65  % (28683)Memory used [KB]: 11257
% 2.26/0.65  % (28683)Time elapsed: 0.222 s
% 2.26/0.65  % (28683)------------------------------
% 2.26/0.65  % (28683)------------------------------
% 2.26/0.65  % (28655)Success in time 0.289 s
%------------------------------------------------------------------------------
