%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 283 expanded)
%              Number of equality atoms :   38 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f51,f55,f59,f63,f70,f88,f118,f216,f229,f234])).

fof(f234,plain,
    ( spl2_1
    | ~ spl2_35 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl2_1
    | ~ spl2_35 ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1)
    | spl2_1
    | ~ spl2_35 ),
    inference(superposition,[],[f29,f228])).

fof(f228,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl2_35
  <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f29,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f229,plain,
    ( spl2_35
    | ~ spl2_13
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f225,f214,f86,f227])).

fof(f86,plain,
    ( spl2_13
  <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f214,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f225,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_13
    | ~ spl2_32 ),
    inference(resolution,[],[f215,f87])).

fof(f87,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1)
        | k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1)) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f210,f116,f32,f214])).

fof(f32,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f116,plain,
    ( spl2_18
  <=> ! [X3,X5,X4] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5)
        | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1) )
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f117,f34])).

fof(f34,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f117,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl2_18
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f105,f61,f53,f116])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f61,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f105,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5)
        | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4))
        | ~ v1_relat_1(X4) )
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f88,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f84,f68,f49,f41,f37,f32,f86])).

fof(f37,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f84,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f83,f42])).

fof(f42,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f83,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f82,f34])).

fof(f82,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f79,f38])).

fof(f38,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f79,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0)))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(superposition,[],[f50,f69])).

fof(f69,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f64,f57,f32,f68])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f64,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f63,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f27])).

fof(f18,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (2423)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (2424)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (2423)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f235,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f51,f55,f59,f63,f70,f88,f118,f216,f229,f234])).
% 0.21/0.42  fof(f234,plain,(
% 0.21/0.42    spl2_1 | ~spl2_35),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.42  fof(f233,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_35)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f232])).
% 0.21/0.42  fof(f232,plain,(
% 0.21/0.42    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) | (spl2_1 | ~spl2_35)),
% 0.21/0.42    inference(superposition,[],[f29,f228])).
% 0.21/0.42  fof(f228,plain,(
% 0.21/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | ~spl2_35),
% 0.21/0.42    inference(avatar_component_clause,[],[f227])).
% 0.21/0.42  fof(f227,plain,(
% 0.21/0.42    spl2_35 <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_1 <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f229,plain,(
% 0.21/0.42    spl2_35 | ~spl2_13 | ~spl2_32),
% 0.21/0.42    inference(avatar_split_clause,[],[f225,f214,f86,f227])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl2_13 <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f214,plain,(
% 0.21/0.42    spl2_32 <=> ! [X1,X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.42  fof(f225,plain,(
% 0.21/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | (~spl2_13 | ~spl2_32)),
% 0.21/0.42    inference(resolution,[],[f215,f87])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f215,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1) | k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1))) ) | ~spl2_32),
% 0.21/0.42    inference(avatar_component_clause,[],[f214])).
% 0.21/0.42  fof(f216,plain,(
% 0.21/0.42    spl2_32 | ~spl2_2 | ~spl2_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f210,f116,f32,f214])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl2_18 <=> ! [X3,X5,X4] : (~r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5) | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4)) | ~v1_relat_1(X4))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relat_1(X0,sK1) = k8_relat_1(X1,k8_relat_1(X0,sK1)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X1)) ) | (~spl2_2 | ~spl2_18)),
% 0.21/0.42    inference(resolution,[],[f117,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4)) | ~r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5)) ) | ~spl2_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f116])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl2_18 | ~spl2_7 | ~spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f105,f61,f53,f116])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl2_9 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (~r1_tarski(k2_relat_1(k8_relat_1(X3,X4)),X5) | k8_relat_1(X3,X4) = k8_relat_1(X5,k8_relat_1(X3,X4)) | ~v1_relat_1(X4)) ) | (~spl2_7 | ~spl2_9)),
% 0.21/0.42    inference(resolution,[],[f62,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) ) | ~spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl2_13 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f84,f68,f49,f41,f37,f32,f86])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_10 <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_10)),
% 0.21/0.42    inference(forward_demodulation,[],[f83,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_10)),
% 0.21/0.42    inference(subsumption_resolution,[],[f82,f34])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_6 | ~spl2_10)),
% 0.21/0.42    inference(subsumption_resolution,[],[f79,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) ) | (~spl2_6 | ~spl2_10)),
% 0.21/0.42    inference(superposition,[],[f50,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl2_10 | ~spl2_2 | ~spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f57,f32,f68])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.42    inference(resolution,[],[f58,f34])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1)) => (k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f27])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2423)------------------------------
% 0.21/0.42  % (2423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2423)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2423)Memory used [KB]: 10618
% 0.21/0.42  % (2423)Time elapsed: 0.008 s
% 0.21/0.42  % (2423)------------------------------
% 0.21/0.42  % (2423)------------------------------
% 0.21/0.42  % (2417)Success in time 0.064 s
%------------------------------------------------------------------------------
