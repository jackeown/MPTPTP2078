%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  84 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 280 expanded)
%              Number of equality atoms :   26 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f42,f51])).

fof(f51,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | ~ spl2_2 ),
    inference(global_subsumption,[],[f18,f32,f48])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f47,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f45,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f45,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(global_subsumption,[],[f17,f44])).

fof(f44,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f20,f32])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f32,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f18,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl2_1 ),
    inference(global_subsumption,[],[f18,f17,f28,f40])).

fof(f40,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl2_1 ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f33,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f19,f30,f26])).

fof(f19,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:51:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (23668)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (23671)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (23672)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.42  % (23672)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f33,f42,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~spl2_2),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    $false | ~spl2_2),
% 0.20/0.42    inference(global_subsumption,[],[f18,f32,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.20/0.42    inference(resolution,[],[f47,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    r1_xboole_0(k1_tarski(sK0),k2_relat_1(sK1)) | ~spl2_2),
% 0.20/0.42    inference(resolution,[],[f45,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl2_2),
% 0.20/0.42    inference(global_subsumption,[],[f17,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.42    inference(superposition,[],[f20,f32])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f5])).
% 0.20/0.42  fof(f5,conjecture,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl2_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    $false | spl2_1),
% 0.20/0.42    inference(global_subsumption,[],[f18,f17,f28,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | spl2_1),
% 0.20/0.42    inference(resolution,[],[f39,f28])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.42    inference(resolution,[],[f21,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,k1_tarski(X0)) | r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(resolution,[],[f22,f23])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    spl2_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ~spl2_1 | spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f30,f26])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (23672)------------------------------
% 0.20/0.42  % (23672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (23672)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (23672)Memory used [KB]: 10618
% 0.20/0.42  % (23672)Time elapsed: 0.005 s
% 0.20/0.42  % (23672)------------------------------
% 0.20/0.42  % (23672)------------------------------
% 0.20/0.43  % (23660)Success in time 0.075 s
%------------------------------------------------------------------------------
