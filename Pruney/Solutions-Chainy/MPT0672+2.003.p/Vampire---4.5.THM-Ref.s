%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 163 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 457 expanded)
%              Number of equality atoms :   36 ( 164 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f50,f259])).

fof(f259,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f249,f36])).

fof(f36,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f249,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f245,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f245,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k8_relat_1(X3,sK2) = k8_relat_1(X4,k8_relat_1(X3,sK2)) ) ),
    inference(subsumption_resolution,[],[f236,f135])).

fof(f135,plain,(
    ! [X6] : v1_relat_1(k8_relat_1(X6,sK2)) ),
    inference(superposition,[],[f52,f124])).

fof(f124,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f43,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f52,plain,(
    ! [X2,X3] : v1_relat_1(k8_relat_1(X2,k8_relat_1(X3,sK2))) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f48,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k8_relat_1(X2,k8_relat_1(X3,sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f23,f44])).

fof(f44,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f236,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(k8_relat_1(X3,sK2))
      | k8_relat_1(X3,sK2) = k8_relat_1(X4,k8_relat_1(X3,sK2)) ) ),
    inference(resolution,[],[f42,f138])).

fof(f138,plain,(
    ! [X7] : r1_tarski(k2_relat_1(k8_relat_1(X7,sK2)),X7) ),
    inference(subsumption_resolution,[],[f136,f135])).

fof(f136,plain,(
    ! [X7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X7,sK2)),X7)
      | ~ v1_relat_1(k8_relat_1(X7,sK2)) ) ),
    inference(superposition,[],[f24,f124])).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r1_tarski(k2_relat_1(X2),X4)
      | ~ v1_relat_1(X2)
      | k8_relat_1(X3,X2) = X2 ) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f32,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f34,f30])).

fof(f20,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (9434)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (9439)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (9434)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f260,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f37,f50,f259])).
% 0.22/0.43  fof(f259,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.43  fof(f258,plain,(
% 0.22/0.43    $false | spl3_2),
% 0.22/0.43    inference(subsumption_resolution,[],[f249,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_2 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f249,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.43    inference(resolution,[],[f245,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.22/0.43    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.43  fof(f8,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.22/0.43    inference(negated_conjecture,[],[f7])).
% 0.22/0.43  fof(f7,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).
% 0.22/0.43  fof(f245,plain,(
% 0.22/0.43    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k8_relat_1(X3,sK2) = k8_relat_1(X4,k8_relat_1(X3,sK2))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f236,f135])).
% 0.22/0.43  fof(f135,plain,(
% 0.22/0.43    ( ! [X6] : (v1_relat_1(k8_relat_1(X6,sK2))) )),
% 0.22/0.43    inference(superposition,[],[f52,f124])).
% 0.22/0.43  fof(f124,plain,(
% 0.22/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) )),
% 0.22/0.43    inference(resolution,[],[f43,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f41,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(resolution,[],[f25,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X2,X3] : (v1_relat_1(k8_relat_1(X2,k8_relat_1(X3,sK2)))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f48,f21])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X2,X3] : (v1_relat_1(k8_relat_1(X2,k8_relat_1(X3,sK2))) | ~v1_relat_1(sK2)) )),
% 0.22/0.43    inference(superposition,[],[f23,f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) )),
% 0.22/0.43    inference(resolution,[],[f27,f21])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.22/0.43  fof(f236,plain,(
% 0.22/0.43    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~v1_relat_1(k8_relat_1(X3,sK2)) | k8_relat_1(X3,sK2) = k8_relat_1(X4,k8_relat_1(X3,sK2))) )),
% 0.22/0.43    inference(resolution,[],[f42,f138])).
% 0.22/0.43  fof(f138,plain,(
% 0.22/0.43    ( ! [X7] : (r1_tarski(k2_relat_1(k8_relat_1(X7,sK2)),X7)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f136,f135])).
% 0.22/0.43  fof(f136,plain,(
% 0.22/0.43    ( ! [X7] : (r1_tarski(k2_relat_1(k8_relat_1(X7,sK2)),X7) | ~v1_relat_1(k8_relat_1(X7,sK2))) )),
% 0.22/0.43    inference(superposition,[],[f24,f124])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | ~r1_tarski(k2_relat_1(X2),X4) | ~v1_relat_1(X2) | k8_relat_1(X3,X2) = X2) )),
% 0.22/0.43    inference(resolution,[],[f25,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl3_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    $false | spl3_1),
% 0.22/0.43    inference(subsumption_resolution,[],[f46,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.22/0.43    inference(superposition,[],[f44,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(resolution,[],[f26,f22])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ~spl3_1 | ~spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f34,f30])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (9434)------------------------------
% 0.22/0.43  % (9434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (9434)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (9434)Memory used [KB]: 10746
% 0.22/0.43  % (9434)Time elapsed: 0.013 s
% 0.22/0.43  % (9434)------------------------------
% 0.22/0.43  % (9434)------------------------------
% 0.22/0.43  % (9433)Success in time 0.072 s
%------------------------------------------------------------------------------
