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
% DateTime   : Thu Dec  3 12:45:40 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 111 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  208 ( 300 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f42,f46,f58,f66,f70,f74,f79,f97,f112,f135,f153,f159,f164])).

fof(f164,plain,
    ( ~ spl2_4
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_26 ),
    inference(resolution,[],[f158,f45])).

fof(f45,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f158,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_26
  <=> ! [X0] : r2_hidden(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f159,plain,
    ( spl2_26
    | ~ spl2_15
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f154,f150,f95,f157])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f150,plain,
    ( spl2_25
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f154,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl2_15
    | ~ spl2_25 ),
    inference(resolution,[],[f152,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f152,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f138,f132,f35,f150])).

fof(f35,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f132,plain,
    ( spl2_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f138,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_22 ),
    inference(superposition,[],[f37,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f132])).

fof(f37,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f135,plain,
    ( spl2_22
    | spl2_1
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f130,f110,f35,f30,f132])).

fof(f30,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f110,plain,
    ( spl2_18
  <=> ! [X1,X2] :
        ( k1_xboole_0 = X1
        | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | spl2_1
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f128,f32])).

fof(f32,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f128,plain,
    ( m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | k1_xboole_0 = sK1
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f111,f37])).

fof(f111,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
        | k1_xboole_0 = X1 )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl2_18
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f104,f77,f64,f110])).

fof(f64,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f77,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f104,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = X1
        | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X1) )
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(resolution,[],[f65,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k1_xboole_0 = X0
        | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f92,f68,f40,f95])).

fof(f40,plain,
    ( spl2_3
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,X1) )
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f79,plain,
    ( spl2_12
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f75,f72,f56,f77])).

fof(f56,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f72,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f57,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f74,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f70,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f66,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f58,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (30746)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (30747)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.42  % (30746)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f165,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f33,f38,f42,f46,f58,f66,f70,f74,f79,f97,f112,f135,f153,f159,f164])).
% 0.14/0.42  fof(f164,plain,(
% 0.14/0.42    ~spl2_4 | ~spl2_26),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f161])).
% 0.14/0.42  fof(f161,plain,(
% 0.14/0.42    $false | (~spl2_4 | ~spl2_26)),
% 0.14/0.42    inference(resolution,[],[f158,f45])).
% 0.14/0.42  fof(f45,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl2_4),
% 0.14/0.42    inference(avatar_component_clause,[],[f44])).
% 0.14/0.42  fof(f44,plain,(
% 0.14/0.42    spl2_4 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.14/0.42  fof(f158,plain,(
% 0.14/0.42    ( ! [X0] : (r2_hidden(sK0,X0)) ) | ~spl2_26),
% 0.14/0.42    inference(avatar_component_clause,[],[f157])).
% 0.14/0.42  fof(f157,plain,(
% 0.14/0.42    spl2_26 <=> ! [X0] : r2_hidden(sK0,X0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.14/0.42  fof(f159,plain,(
% 0.14/0.42    spl2_26 | ~spl2_15 | ~spl2_25),
% 0.14/0.42    inference(avatar_split_clause,[],[f154,f150,f95,f157])).
% 0.14/0.42  fof(f95,plain,(
% 0.14/0.42    spl2_15 <=> ! [X1,X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.14/0.42  fof(f150,plain,(
% 0.14/0.42    spl2_25 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.14/0.42  fof(f154,plain,(
% 0.14/0.42    ( ! [X0] : (r2_hidden(sK0,X0)) ) | (~spl2_15 | ~spl2_25)),
% 0.14/0.42    inference(resolution,[],[f152,f96])).
% 0.14/0.42  fof(f96,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) ) | ~spl2_15),
% 0.14/0.42    inference(avatar_component_clause,[],[f95])).
% 0.14/0.42  fof(f152,plain,(
% 0.14/0.42    r2_hidden(sK0,k1_xboole_0) | ~spl2_25),
% 0.14/0.42    inference(avatar_component_clause,[],[f150])).
% 0.14/0.42  fof(f153,plain,(
% 0.14/0.42    spl2_25 | ~spl2_2 | ~spl2_22),
% 0.14/0.42    inference(avatar_split_clause,[],[f138,f132,f35,f150])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.14/0.42  fof(f132,plain,(
% 0.14/0.42    spl2_22 <=> k1_xboole_0 = sK1),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.14/0.42  fof(f138,plain,(
% 0.14/0.42    r2_hidden(sK0,k1_xboole_0) | (~spl2_2 | ~spl2_22)),
% 0.14/0.42    inference(superposition,[],[f37,f134])).
% 0.14/0.42  fof(f134,plain,(
% 0.14/0.42    k1_xboole_0 = sK1 | ~spl2_22),
% 0.14/0.42    inference(avatar_component_clause,[],[f132])).
% 0.14/0.42  fof(f37,plain,(
% 0.14/0.42    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.14/0.42    inference(avatar_component_clause,[],[f35])).
% 0.14/0.42  fof(f135,plain,(
% 0.14/0.42    spl2_22 | spl2_1 | ~spl2_2 | ~spl2_18),
% 0.14/0.42    inference(avatar_split_clause,[],[f130,f110,f35,f30,f132])).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    spl2_1 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.14/0.42  fof(f110,plain,(
% 0.14/0.42    spl2_18 <=> ! [X1,X2] : (k1_xboole_0 = X1 | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) | ~r2_hidden(X2,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.14/0.42  fof(f130,plain,(
% 0.14/0.42    k1_xboole_0 = sK1 | (spl2_1 | ~spl2_2 | ~spl2_18)),
% 0.14/0.42    inference(subsumption_resolution,[],[f128,f32])).
% 0.14/0.42  fof(f32,plain,(
% 0.14/0.42    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl2_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f30])).
% 0.14/0.42  fof(f128,plain,(
% 0.14/0.42    m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | k1_xboole_0 = sK1 | (~spl2_2 | ~spl2_18)),
% 0.14/0.42    inference(resolution,[],[f111,f37])).
% 0.14/0.42  fof(f111,plain,(
% 0.14/0.42    ( ! [X2,X1] : (~r2_hidden(X2,X1) | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) | k1_xboole_0 = X1) ) | ~spl2_18),
% 0.14/0.42    inference(avatar_component_clause,[],[f110])).
% 0.14/0.42  fof(f112,plain,(
% 0.14/0.42    spl2_18 | ~spl2_9 | ~spl2_12),
% 0.14/0.42    inference(avatar_split_clause,[],[f104,f77,f64,f110])).
% 0.14/0.42  fof(f64,plain,(
% 0.14/0.42    spl2_9 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.14/0.42  fof(f77,plain,(
% 0.14/0.42    spl2_12 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.14/0.42  fof(f104,plain,(
% 0.14/0.42    ( ! [X2,X1] : (k1_xboole_0 = X1 | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) | ~r2_hidden(X2,X1)) ) | (~spl2_9 | ~spl2_12)),
% 0.14/0.42    inference(resolution,[],[f65,f78])).
% 0.14/0.42  fof(f78,plain,(
% 0.14/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) ) | ~spl2_12),
% 0.14/0.42    inference(avatar_component_clause,[],[f77])).
% 0.14/0.42  fof(f65,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) ) | ~spl2_9),
% 0.14/0.42    inference(avatar_component_clause,[],[f64])).
% 0.14/0.42  fof(f97,plain,(
% 0.14/0.42    spl2_15 | ~spl2_3 | ~spl2_10),
% 0.14/0.42    inference(avatar_split_clause,[],[f92,f68,f40,f95])).
% 0.14/0.42  fof(f40,plain,(
% 0.14/0.42    spl2_3 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.14/0.42  fof(f68,plain,(
% 0.14/0.42    spl2_10 <=> ! [X1,X0,X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.14/0.42  fof(f92,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) ) | (~spl2_3 | ~spl2_10)),
% 0.14/0.42    inference(resolution,[],[f69,f41])).
% 0.14/0.42  fof(f41,plain,(
% 0.14/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_3),
% 0.14/0.42    inference(avatar_component_clause,[],[f40])).
% 0.14/0.42  fof(f69,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) ) | ~spl2_10),
% 0.14/0.42    inference(avatar_component_clause,[],[f68])).
% 0.14/0.42  fof(f79,plain,(
% 0.14/0.42    spl2_12 | ~spl2_7 | ~spl2_11),
% 0.14/0.42    inference(avatar_split_clause,[],[f75,f72,f56,f77])).
% 0.14/0.42  fof(f56,plain,(
% 0.14/0.42    spl2_7 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.14/0.42  fof(f72,plain,(
% 0.14/0.42    spl2_11 <=> ! [X1,X0] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.14/0.42  fof(f75,plain,(
% 0.14/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) ) | (~spl2_7 | ~spl2_11)),
% 0.14/0.42    inference(subsumption_resolution,[],[f57,f73])).
% 0.14/0.42  fof(f73,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | ~spl2_11),
% 0.14/0.42    inference(avatar_component_clause,[],[f72])).
% 0.14/0.42  fof(f57,plain,(
% 0.14/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_7),
% 0.14/0.42    inference(avatar_component_clause,[],[f56])).
% 0.14/0.42  fof(f74,plain,(
% 0.14/0.42    spl2_11),
% 0.14/0.42    inference(avatar_split_clause,[],[f28,f72])).
% 0.14/0.42  fof(f28,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.14/0.42  fof(f70,plain,(
% 0.14/0.42    spl2_10),
% 0.14/0.42    inference(avatar_split_clause,[],[f27,f68])).
% 0.14/0.42  fof(f27,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.14/0.42  fof(f66,plain,(
% 0.14/0.42    spl2_9),
% 0.14/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.14/0.42    inference(flattening,[],[f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.14/0.42  fof(f58,plain,(
% 0.14/0.42    spl2_7),
% 0.14/0.42    inference(avatar_split_clause,[],[f23,f56])).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.14/0.42    inference(nnf_transformation,[],[f10])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.14/0.42  fof(f46,plain,(
% 0.14/0.42    spl2_4),
% 0.14/0.42    inference(avatar_split_clause,[],[f21,f44])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.14/0.42  fof(f42,plain,(
% 0.14/0.42    spl2_3),
% 0.14/0.42    inference(avatar_split_clause,[],[f20,f40])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.14/0.42  fof(f38,plain,(
% 0.14/0.42    spl2_2),
% 0.14/0.42    inference(avatar_split_clause,[],[f18,f35])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    r2_hidden(sK0,sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f9,plain,(
% 0.14/0.42    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f8])).
% 0.14/0.42  fof(f8,negated_conjecture,(
% 0.14/0.42    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.14/0.42    inference(negated_conjecture,[],[f7])).
% 0.14/0.42  fof(f7,conjecture,(
% 0.14/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.14/0.42  fof(f33,plain,(
% 0.14/0.42    ~spl2_1),
% 0.14/0.42    inference(avatar_split_clause,[],[f19,f30])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (30746)------------------------------
% 0.14/0.42  % (30746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (30746)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (30746)Memory used [KB]: 10618
% 0.14/0.42  % (30746)Time elapsed: 0.008 s
% 0.14/0.42  % (30746)------------------------------
% 0.14/0.42  % (30746)------------------------------
% 0.14/0.43  % (30740)Success in time 0.065 s
%------------------------------------------------------------------------------
