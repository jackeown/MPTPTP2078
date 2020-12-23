%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  230 ( 429 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f61,f65,f69,f89,f93,f97,f108,f122,f129,f173,f181])).

fof(f181,plain,
    ( ~ spl2_6
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f88,f172,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f172,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_23
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f88,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_11
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f173,plain,
    ( spl2_23
    | spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f143,f126,f119,f106,f44,f39,f170])).

fof(f39,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f44,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f106,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f119,plain,
    ( spl2_16
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f126,plain,
    ( spl2_17
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f143,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f41,f46,f121,f128,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f128,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f121,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f46,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f41,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f129,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_17
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f99,f91,f54,f126,f49,f39])).

fof(f49,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f54,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f91,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f99,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f56,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f56,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f122,plain,
    ( spl2_16
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f104,f95,f91,f49,f39,f119])).

fof(f95,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f104,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f100,f98])).

fof(f98,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f41,f51,f92])).

fof(f51,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f100,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f41,f51,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f108,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f32,f106])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f97,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f93,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f89,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f67,f59,f87])).

fof(f59,plain,
    ( spl2_5
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( spl2_7
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f68,f60])).

fof(f60,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f68,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f65,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (28576)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.42  % (28576)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f183,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f61,f65,f69,f89,f93,f97,f108,f122,f129,f173,f181])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    ~spl2_6 | ~spl2_11 | ~spl2_23),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    $false | (~spl2_6 | ~spl2_11 | ~spl2_23)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f88,f172,f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl2_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    v1_xboole_0(k1_tarski(sK1)) | ~spl2_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f170])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    spl2_23 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl2_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl2_11 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    spl2_23 | spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_16 | ~spl2_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f143,f126,f119,f106,f44,f39,f170])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    spl2_14 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl2_16 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    spl2_17 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    v1_xboole_0(k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_16 | ~spl2_17)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f41,f46,f121,f128,f107])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f106])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f126])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f119])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~v1_xboole_0(sK0) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl2_1 | ~spl2_3 | spl2_17 | ~spl2_4 | ~spl2_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f99,f91,f54,f126,f49,f39])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl2_12 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_12)),
% 0.21/0.43    inference(superposition,[],[f56,f92])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f91])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    spl2_16 | spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f104,f95,f91,f49,f39,f119])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl2_13 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_13)),
% 0.21/0.43    inference(forward_demodulation,[],[f100,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3 | ~spl2_12)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f41,f51,f92])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_13)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f41,f51,f96])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f95])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    spl2_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f106])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl2_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl2_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f91])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl2_11 | ~spl2_5 | ~spl2_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f73,f67,f59,f87])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl2_5 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl2_7 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl2_5 | ~spl2_7)),
% 0.21/0.43    inference(superposition,[],[f68,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f59])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl2_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f67])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f63])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f54])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.43    inference(negated_conjecture,[],[f10])).
% 0.21/0.43  fof(f10,conjecture,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    m1_subset_1(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f44])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    v1_zfmisc_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f39])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~v1_xboole_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (28576)------------------------------
% 0.21/0.43  % (28576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (28576)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (28576)Memory used [KB]: 6140
% 0.21/0.43  % (28576)Time elapsed: 0.009 s
% 0.21/0.43  % (28576)------------------------------
% 0.21/0.43  % (28576)------------------------------
% 0.21/0.43  % (28570)Success in time 0.073 s
%------------------------------------------------------------------------------
