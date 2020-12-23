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
% DateTime   : Thu Dec  3 13:20:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 131 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  250 ( 433 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f52,f56,f60,f64,f68,f76,f88,f98,f104,f109])).

fof(f109,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f107,f75])).

fof(f75,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_10
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f107,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f106,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f105,f32])).

fof(f32,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f105,plain,
    ( ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(resolution,[],[f103,f97])).

fof(f97,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_14
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f104,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f100,f58,f54,f50,f102])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f51,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | v1_xboole_0(k1_tarski(X0))
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f98,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f85,f35,f95])).

fof(f35,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_12
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f37,f87])).

fof(f87,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f37,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f88,plain,
    ( spl2_12
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f83,f66,f45,f40,f85])).

fof(f40,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f83,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f81,f47])).

fof(f81,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f67,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k1_tarski(X1)
        | v1_xboole_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f76,plain,
    ( spl2_10
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f62,f45,f40,f73])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f69,f47])).

fof(f69,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f48,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:59:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (11979)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (11980)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (11983)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (11983)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f52,f56,f60,f64,f68,f76,f88,f98,f104,f109])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ~spl2_1 | spl2_4 | ~spl2_10 | ~spl2_14 | ~spl2_15),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    $false | (~spl2_1 | spl2_4 | ~spl2_10 | ~spl2_14 | ~spl2_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f107,f75])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    r2_hidden(sK1,sK0) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f73])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl2_10 <=> r2_hidden(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    ~r2_hidden(sK1,sK0) | (~spl2_1 | spl2_4 | ~spl2_14 | ~spl2_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f106,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0) | spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_4 <=> v1_xboole_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | ~r2_hidden(sK1,sK0) | (~spl2_1 | ~spl2_14 | ~spl2_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f105,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    v1_zfmisc_1(sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl2_1 <=> v1_zfmisc_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | ~r2_hidden(sK1,sK0) | (~spl2_14 | ~spl2_15)),
% 0.20/0.42    inference(resolution,[],[f103,f97])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f95])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    spl2_14 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | ~spl2_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f102])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl2_15 <=> ! [X1,X0] : (~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    spl2_15 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f100,f58,f54,f50,f102])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl2_5 <=> ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl2_6 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | (~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.20/0.42    inference(subsumption_resolution,[],[f99,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_subset_1(k1_tarski(X0),X1) | v1_xboole_0(k1_tarski(X0)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | (~spl2_6 | ~spl2_7)),
% 0.20/0.42    inference(resolution,[],[f55,f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f58])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f54])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    spl2_14 | ~spl2_2 | ~spl2_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f93,f85,f35,f95])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl2_2 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl2_12 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    v1_subset_1(k1_tarski(sK1),sK0) | (~spl2_2 | ~spl2_12)),
% 0.20/0.42    inference(backward_demodulation,[],[f37,f87])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl2_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f85])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    spl2_12 | ~spl2_3 | spl2_4 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f66,f45,f40,f85])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl2_9 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (~spl2_3 | spl2_4 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f81,f47])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f67,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl2_10 | ~spl2_3 | spl2_4 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f71,f62,f45,f40,f73])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl2_8 <=> ! [X1,X0] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    r2_hidden(sK1,sK0) | (~spl2_3 | spl2_4 | ~spl2_8)),
% 0.20/0.42    inference(subsumption_resolution,[],[f69,f47])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | r2_hidden(sK1,sK0) | (~spl2_3 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f63,f42])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f66])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f62])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f54])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f50])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f45])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f40])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    m1_subset_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f35])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f30])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    v1_zfmisc_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (11983)------------------------------
% 0.20/0.42  % (11983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (11983)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (11983)Memory used [KB]: 6140
% 0.20/0.42  % (11983)Time elapsed: 0.005 s
% 0.20/0.42  % (11983)------------------------------
% 0.20/0.42  % (11983)------------------------------
% 0.20/0.43  % (11974)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (11982)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (11972)Success in time 0.075 s
%------------------------------------------------------------------------------
