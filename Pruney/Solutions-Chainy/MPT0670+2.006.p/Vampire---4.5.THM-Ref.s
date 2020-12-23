%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 107 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 ( 382 expanded)
%              Number of equality atoms :   25 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f59,f124])).

fof(f124,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl5_2 ),
    inference(global_subsumption,[],[f29,f120])).

fof(f120,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f117,f82])).

fof(f82,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(k6_relat_1(sK3),k1_funct_1(sK4,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> sP0(sK3,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_funct_1(X2,X1) = k1_funct_1(k6_relat_1(X0),k1_funct_1(X2,X1)) ) ),
    inference(resolution,[],[f38,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(k1_funct_1(X2,X1),X0)
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X1),X0)
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f117,plain,(
    k1_funct_1(k8_relat_1(sK3,sK4),sK2) = k1_funct_1(k6_relat_1(sK3),k1_funct_1(sK4,sK2)) ),
    inference(resolution,[],[f67,f28])).

fof(f28,plain,(
    r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
        & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
      & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK4)))
      | k1_funct_1(k6_relat_1(X0),k1_funct_1(sK4,X1)) = k1_funct_1(k8_relat_1(X0,sK4),X1) ) ),
    inference(global_subsumption,[],[f27,f26,f31,f30,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK4)))
      | k1_funct_1(k6_relat_1(X0),k1_funct_1(sK4,X1)) = k1_funct_1(k8_relat_1(X0,sK4),X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f34,f43])).

fof(f43,plain,(
    ! [X0] : k8_relat_1(X0,sK4) = k5_relat_1(sK4,k6_relat_1(X0)) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl5_1 ),
    inference(global_subsumption,[],[f27,f26,f57])).

fof(f57,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f15,f17,f16])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f51,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> sP1(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f46,f53,f49])).

fof(f46,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ sP1(sK4,sK2,sK3) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (12511)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (12514)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (12518)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.44  % (12512)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (12518)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f56,f59,f124])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    ~spl5_2),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.44  fof(f123,plain,(
% 0.22/0.44    $false | ~spl5_2),
% 0.22/0.44    inference(global_subsumption,[],[f29,f120])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) | ~spl5_2),
% 0.22/0.44    inference(forward_demodulation,[],[f117,f82])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    k1_funct_1(sK4,sK2) = k1_funct_1(k6_relat_1(sK3),k1_funct_1(sK4,sK2)) | ~spl5_2),
% 0.22/0.44    inference(resolution,[],[f42,f55])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    sP0(sK3,sK2,sK4) | ~spl5_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl5_2 <=> sP0(sK3,sK2,sK4)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_funct_1(X2,X1) = k1_funct_1(k6_relat_1(X0),k1_funct_1(X2,X1))) )),
% 0.22/0.44    inference(resolution,[],[f38,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X1),X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.44    inference(rectify,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.44    inference(flattening,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.44    inference(nnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))))),
% 0.22/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    k1_funct_1(k8_relat_1(sK3,sK4),sK2) = k1_funct_1(k6_relat_1(sK3),k1_funct_1(sK4,sK2))),
% 0.22/0.44    inference(resolution,[],[f67,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK4))) | k1_funct_1(k6_relat_1(X0),k1_funct_1(sK4,X1)) = k1_funct_1(k8_relat_1(X0,sK4),X1)) )),
% 0.22/0.44    inference(global_subsumption,[],[f27,f26,f31,f30,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k8_relat_1(X0,sK4))) | k1_funct_1(k6_relat_1(X0),k1_funct_1(sK4,X1)) = k1_funct_1(k8_relat_1(X0,sK4),X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f34,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(X0,sK4) = k5_relat_1(sK4,k6_relat_1(X0))) )),
% 0.22/0.44    inference(resolution,[],[f32,f26])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    v1_relat_1(sK4)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    v1_funct_1(sK4)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl5_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    $false | spl5_1),
% 0.22/0.44    inference(global_subsumption,[],[f27,f26,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_1),
% 0.22/0.44    inference(resolution,[],[f51,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (sP1(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(definition_folding,[],[f15,f17,f16])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X2,X0,X1] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.22/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ~sP1(sK4,sK2,sK3) | spl5_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl5_1 <=> sP1(sK4,sK2,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ~spl5_1 | spl5_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f46,f53,f49])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    sP0(sK3,sK2,sK4) | ~sP1(sK4,sK2,sK3)),
% 0.22/0.44    inference(resolution,[],[f35,f28])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X0))))) | ~sP1(X0,X1,X2))),
% 0.22/0.44    inference(rectify,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X2,X0,X1] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~sP1(X2,X0,X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f17])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (12518)------------------------------
% 0.22/0.44  % (12518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (12518)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (12518)Memory used [KB]: 10746
% 0.22/0.44  % (12518)Time elapsed: 0.010 s
% 0.22/0.44  % (12518)------------------------------
% 0.22/0.44  % (12518)------------------------------
% 0.22/0.45  % (12506)Success in time 0.081 s
%------------------------------------------------------------------------------
