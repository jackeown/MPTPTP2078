%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 395 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f81,f90,f97,f110,f125,f133,f147])).

fof(f147,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f58,f139])).

fof(f139,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_1
    | ~ spl2_19 ),
    inference(superposition,[],[f38,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f38,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f133,plain,
    ( spl2_19
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f126,f123,f106,f61,f46,f41,f36,f130])).

fof(f41,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( spl2_6
  <=> ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( spl2_15
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f123,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( v1_xboole_0(k1_tarski(X0))
        | ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f38,f43,f48,f62,f108,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k1_tarski(X0),X1)
        | v1_xboole_0(k1_tarski(X0))
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f108,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f62,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f48,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f43,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f125,plain,
    ( spl2_18
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f98,f95,f79,f123])).

fof(f79,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f95,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_tarski(X0))
        | ~ v1_subset_1(k1_tarski(X0),X1)
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) )
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f110,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_15
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f88,f51,f106,f46,f36])).

fof(f51,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_tarski(X1) = k6_domain_1(X0,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f53,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X1) = k6_domain_1(X0,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f53,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f97,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f81,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f63,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:16:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (32652)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (32652)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f63,f81,f90,f97,f110,f125,f133,f147])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl2_1 | ~spl2_5 | ~spl2_19),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    $false | (spl2_1 | ~spl2_5 | ~spl2_19)),
% 0.22/0.48    inference(subsumption_resolution,[],[f58,f139])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (spl2_1 | ~spl2_19)),
% 0.22/0.48    inference(superposition,[],[f38,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl2_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f130])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl2_19 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl2_1 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl2_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl2_19 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_15 | ~spl2_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f126,f123,f106,f61,f46,f41,f36,f130])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl2_6 <=> ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl2_15 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    spl2_18 <=> ! [X1,X0] : (v1_xboole_0(k1_tarski(X0)) | ~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_15 | ~spl2_18)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f38,f43,f48,f62,f108,f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_subset_1(k1_tarski(X0),X1) | v1_xboole_0(k1_tarski(X0)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) ) | ~spl2_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f123])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f106])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) ) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl2_18 | ~spl2_10 | ~spl2_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f95,f79,f123])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_13 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(k1_tarski(X0)) | ~v1_subset_1(k1_tarski(X0),X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,X1)) ) | (~spl2_10 | ~spl2_13)),
% 0.22/0.48    inference(resolution,[],[f96,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl2_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl2_1 | ~spl2_3 | spl2_15 | ~spl2_4 | ~spl2_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f93,f88,f51,f106,f46,f36])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl2_12 <=> ! [X1,X0] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_12)),
% 0.22/0.48    inference(superposition,[],[f53,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl2_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f95])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl2_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f88])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl2_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f79])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f61])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f56])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f51])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    m1_subset_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f41])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v1_zfmisc_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f36])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (32652)------------------------------
% 0.22/0.48  % (32652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32652)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (32652)Memory used [KB]: 6140
% 0.22/0.48  % (32652)Time elapsed: 0.044 s
% 0.22/0.48  % (32652)------------------------------
% 0.22/0.48  % (32652)------------------------------
% 0.22/0.49  % (32646)Success in time 0.125 s
%------------------------------------------------------------------------------
