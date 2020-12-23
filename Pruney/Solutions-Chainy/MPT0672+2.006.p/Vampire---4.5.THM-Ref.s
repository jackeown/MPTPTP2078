%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  93 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 274 expanded)
%              Number of equality atoms :   48 (  93 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f57,f62,f66,f71,f74])).

fof(f74,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f24,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(resolution,[],[f70,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_10
  <=> ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f71,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f67,f49,f31,f69])).

fof(f31,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( ! [X0] :
        ( k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( spl3_2
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f63,f60,f54,f26])).

fof(f26,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( spl3_8
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( spl3_9
  <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f63,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f61,f56])).

fof(f56,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f61,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f45,f36,f60])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f58,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f57,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f41,f31,f54])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f26,f22])).

fof(f17,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (29534)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (29533)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (29535)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (29536)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (29536)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f57,f62,f66,f71,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl3_1 | ~spl3_4 | ~spl3_10),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_4 | ~spl3_10)),
% 0.21/0.44    inference(subsumption_resolution,[],[f72,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_4 | ~spl3_10)),
% 0.21/0.44    inference(resolution,[],[f70,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))) ) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl3_10 <=> ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_10 | ~spl3_3 | ~spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f67,f49,f31,f69])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl3_7 <=> ! [X1,X0,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) | ~v1_relat_1(X0)) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.44    inference(resolution,[],[f50,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) ) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl3_2 | ~spl3_8 | ~spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f63,f60,f54,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    spl3_2 <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl3_8 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl3_9 <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) | (~spl3_8 | ~spl3_9)),
% 0.21/0.44    inference(superposition,[],[f61,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f60])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_9 | ~spl3_4 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f58,f45,f36,f60])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl3_6 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.44    inference(resolution,[],[f46,f38])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl3_8 | ~spl3_3 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f41,f31,f54])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_5)),
% 0.21/0.44    inference(resolution,[],[f42,f33])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f41])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f49])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f36])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_relat_1(X2)) => ((k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f31])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f26,f22])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29536)------------------------------
% 0.21/0.44  % (29536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29536)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29536)Memory used [KB]: 6140
% 0.21/0.44  % (29536)Time elapsed: 0.008 s
% 0.21/0.44  % (29536)------------------------------
% 0.21/0.44  % (29536)------------------------------
% 0.21/0.44  % (29525)Success in time 0.085 s
%------------------------------------------------------------------------------
