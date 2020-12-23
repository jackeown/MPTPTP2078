%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 125 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 476 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f52,f68,f81,f159,f198,f239])).

fof(f239,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f237,f201])).

fof(f201,plain,
    ( ~ v1_finset_1(sK2(sK0))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f38,f41,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK2(X0))
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f41,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f237,plain,
    ( v1_finset_1(sK2(sK0))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f236,f38])).

fof(f236,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(sK2(sK0))
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f225,f41])).

fof(f225,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | v1_finset_1(sK2(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f30,f67])).

fof(f67,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | v1_finset_1(X2) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_4
  <=> ! [X2] :
        ( v1_finset_1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f198,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f196,f42])).

fof(f42,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f196,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f193,f51])).

fof(f51,plain,
    ( ~ v1_finset_1(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_3
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f193,plain,
    ( v1_finset_1(sK1)
    | ~ v1_finset_1(k3_tarski(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f165])).

fof(f165,plain,
    ( sK1 = k3_xboole_0(sK1,k3_tarski(sK0))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f162,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f162,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f80,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f80,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

fof(f159,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f147,f37])).

fof(f37,plain,
    ( ~ v1_finset_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f147,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f55,f144])).

fof(f144,plain,(
    ! [X0] : k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
    inference(unit_resulting_resolution,[],[f28,f34])).

fof(f28,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f55,plain,
    ( ! [X0] : v1_finset_1(k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(sK0))))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f44,f32])).

fof(f44,plain,
    ( v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f81,plain,
    ( ~ spl3_1
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f40,f78,f36])).

fof(f26,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ v1_finset_1(X1)
        & r2_hidden(X1,sK0) )
   => ( ~ v1_finset_1(sK1)
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f68,plain,
    ( spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f40,f66])).

fof(f25,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f27,f40,f49,f36])).

fof(f27,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f24,f40,f36])).

fof(f24,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22766)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.41  % (22770)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (22766)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f240,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f43,f52,f68,f81,f159,f198,f239])).
% 0.20/0.41  fof(f239,plain,(
% 0.20/0.41    ~spl3_1 | spl3_2 | ~spl3_4),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.42  fof(f238,plain,(
% 0.20/0.42    $false | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f237,f201])).
% 0.20/0.42  fof(f201,plain,(
% 0.20/0.42    ~v1_finset_1(sK2(sK0)) | (~spl3_1 | spl3_2)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f38,f41,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_finset_1(sK2(X0)) | v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)) | ~v1_finset_1(X0))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.20/0.42    inference(flattening,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ~v1_finset_1(k3_tarski(sK0)) | spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl3_2 <=> v1_finset_1(k3_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    v1_finset_1(sK0) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl3_1 <=> v1_finset_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f237,plain,(
% 0.20/0.42    v1_finset_1(sK2(sK0)) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f236,f38])).
% 0.20/0.42  fof(f236,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | v1_finset_1(sK2(sK0)) | (spl3_2 | ~spl3_4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f225,f41])).
% 0.20/0.42  fof(f225,plain,(
% 0.20/0.42    v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0) | v1_finset_1(sK2(sK0)) | ~spl3_4),
% 0.20/0.42    inference(resolution,[],[f30,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X2] : (~r2_hidden(X2,sK0) | v1_finset_1(X2)) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl3_4 <=> ! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f198,plain,(
% 0.20/0.42    ~spl3_2 | spl3_3 | ~spl3_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.42  fof(f197,plain,(
% 0.20/0.42    $false | (~spl3_2 | spl3_3 | ~spl3_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f196,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    v1_finset_1(k3_tarski(sK0)) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f196,plain,(
% 0.20/0.42    ~v1_finset_1(k3_tarski(sK0)) | (spl3_3 | ~spl3_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f193,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~v1_finset_1(sK1) | spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_3 <=> v1_finset_1(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f193,plain,(
% 0.20/0.42    v1_finset_1(sK1) | ~v1_finset_1(k3_tarski(sK0)) | ~spl3_5),
% 0.20/0.42    inference(superposition,[],[f32,f165])).
% 0.20/0.42  fof(f165,plain,(
% 0.20/0.42    sK1 = k3_xboole_0(sK1,k3_tarski(sK0)) | ~spl3_5),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f162,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.42  fof(f162,plain,(
% 0.20/0.42    r1_tarski(sK1,k3_tarski(sK0)) | ~spl3_5),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f80,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    r2_hidden(sK1,sK0) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl3_5 <=> r2_hidden(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_finset_1(X1) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).
% 0.20/0.42  fof(f159,plain,(
% 0.20/0.42    spl3_1 | ~spl3_2),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f147,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ~v1_finset_1(sK0) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f147,plain,(
% 0.20/0.42    v1_finset_1(sK0) | ~spl3_2),
% 0.20/0.42    inference(superposition,[],[f55,f144])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    ( ! [X0] : (k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0) )),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f28,f34])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0] : (v1_finset_1(k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(sK0))))) ) | ~spl3_2),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f44,f32])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) | ~spl3_2),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f42,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ~spl3_1 | spl3_5 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f40,f78,f36])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ~v1_finset_1(k3_tarski(sK0)) | r2_hidden(sK1,sK0) | ~v1_finset_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    (~v1_finset_1(k3_tarski(sK0)) | (~v1_finset_1(sK1) & r2_hidden(sK1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)))) => ((~v1_finset_1(k3_tarski(sK0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) => (~v1_finset_1(sK1) & r2_hidden(sK1,sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0))))),
% 0.20/0.42    inference(rectify,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.20/0.42    inference(flattening,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.20/0.42    inference(nnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl3_4 | spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f40,f66])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X2] : (v1_finset_1(k3_tarski(sK0)) | v1_finset_1(X2) | ~r2_hidden(X2,sK0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ~spl3_1 | ~spl3_3 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f40,f49,f36])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ~v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK1) | ~v1_finset_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_1 | spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f40,f36])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (22766)------------------------------
% 0.20/0.42  % (22766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (22766)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (22766)Memory used [KB]: 6268
% 0.20/0.42  % (22766)Time elapsed: 0.010 s
% 0.20/0.42  % (22766)------------------------------
% 0.20/0.42  % (22766)------------------------------
% 0.20/0.42  % (22764)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (22763)Success in time 0.065 s
%------------------------------------------------------------------------------
