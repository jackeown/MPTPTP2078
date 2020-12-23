%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 161 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  200 ( 486 expanded)
%              Number of equality atoms :   11 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f128,f130,f149,f160,f173,f176,f179])).

fof(f179,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl2_5 ),
    inference(resolution,[],[f177,f24])).

fof(f24,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

% (3416)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f177,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f144,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f144,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK1,X4)
        | v1_xboole_0(X4) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_5
  <=> ! [X4] :
        ( v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f176,plain,(
    ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl2_8 ),
    inference(resolution,[],[f159,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f159,plain,
    ( v1_xboole_0(k1_enumset1(sK1,sK1,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f173,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f155,f27])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f155,plain,
    ( ~ v1_zfmisc_1(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_7
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f160,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_7
    | spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f150,f146,f157,f153,f46,f42])).

fof(f42,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( spl2_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f146,plain,
    ( spl2_6
  <=> v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f150,plain,
    ( v1_xboole_0(k1_enumset1(sK1,sK1,sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f148,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k1_enumset1(X0,X0,X0),X1)
      | v1_xboole_0(k1_enumset1(X0,X0,X0))
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f148,plain,
    ( v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f149,plain,
    ( spl2_5
    | spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f135,f125,f146,f143])).

fof(f125,plain,
    ( spl2_4
  <=> ! [X0] :
        ( v1_subset_1(k6_domain_1(X0,sK1),sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f135,plain,
    ( ! [X4] :
        ( v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4) )
    | ~ spl2_4 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X4] :
        ( v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4)
        | ~ m1_subset_1(sK1,X4)
        | v1_xboole_0(X4) )
    | ~ spl2_4 ),
    inference(superposition,[],[f126,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f126,plain,
    ( ! [X0] :
        ( v1_subset_1(k6_domain_1(X0,sK1),sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK1,X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f130,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f123,f25])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f128,plain,
    ( spl2_2
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f80,f125,f121,f46])).

fof(f80,plain,(
    ! [X0] :
      ( v1_subset_1(k6_domain_1(X0,sK1),sK0)
      | ~ m1_subset_1(sK1,sK0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f26,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X1,X0) = k6_domain_1(X2,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f39,f39])).

fof(f26,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | ~ spl2_2 ),
    inference(resolution,[],[f48,f24])).

fof(f48,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f40,f46,f42])).

fof(f40,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (3410)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.42  % (3410)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f180,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f49,f53,f128,f130,f149,f160,f173,f176,f179])).
% 0.20/0.42  fof(f179,plain,(
% 0.20/0.42    ~spl2_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f178])).
% 0.20/0.42  fof(f178,plain,(
% 0.20/0.42    $false | ~spl2_5),
% 0.20/0.42    inference(resolution,[],[f177,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f9])).
% 0.20/0.42  % (3416)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.42  fof(f9,conjecture,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.42  fof(f177,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | ~spl2_5),
% 0.20/0.42    inference(resolution,[],[f144,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    m1_subset_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    ( ! [X4] : (~m1_subset_1(sK1,X4) | v1_xboole_0(X4)) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f143])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    spl2_5 <=> ! [X4] : (v1_xboole_0(X4) | ~m1_subset_1(sK1,X4))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f176,plain,(
% 0.20/0.42    ~spl2_8),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.42  fof(f174,plain,(
% 0.20/0.42    $false | ~spl2_8),
% 0.20/0.42    inference(resolution,[],[f159,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f28,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f29,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.42  fof(f159,plain,(
% 0.20/0.42    v1_xboole_0(k1_enumset1(sK1,sK1,sK1)) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f157])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    spl2_8 <=> v1_xboole_0(k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f173,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f172])).
% 0.20/0.42  fof(f172,plain,(
% 0.20/0.42    $false | spl2_7),
% 0.20/0.42    inference(resolution,[],[f155,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    v1_zfmisc_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f155,plain,(
% 0.20/0.42    ~v1_zfmisc_1(sK0) | spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f153])).
% 0.20/0.42  fof(f153,plain,(
% 0.20/0.42    spl2_7 <=> v1_zfmisc_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f160,plain,(
% 0.20/0.42    ~spl2_1 | spl2_2 | ~spl2_7 | spl2_8 | ~spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f150,f146,f157,f153,f46,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_1 <=> r2_hidden(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_2 <=> v1_xboole_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f146,plain,(
% 0.20/0.42    spl2_6 <=> v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f150,plain,(
% 0.20/0.42    v1_xboole_0(k1_enumset1(sK1,sK1,sK1)) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | ~r2_hidden(sK1,sK0) | ~spl2_6),
% 0.20/0.42    inference(resolution,[],[f148,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_subset_1(k1_enumset1(X0,X0,X0),X1) | v1_xboole_0(k1_enumset1(X0,X0,X0)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(resolution,[],[f31,f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f33,f36])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.42  fof(f148,plain,(
% 0.20/0.42    v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f146])).
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    spl2_5 | spl2_6 | ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f135,f125,f146,f143])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    spl2_4 <=> ! [X0] : (v1_subset_1(k6_domain_1(X0,sK1),sK0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f135,plain,(
% 0.20/0.42    ( ! [X4] : (v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0) | v1_xboole_0(X4) | ~m1_subset_1(sK1,X4)) ) | ~spl2_4),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    ( ! [X4] : (v1_subset_1(k1_enumset1(sK1,sK1,sK1),sK0) | v1_xboole_0(X4) | ~m1_subset_1(sK1,X4) | ~m1_subset_1(sK1,X4) | v1_xboole_0(X4)) ) | ~spl2_4),
% 0.20/0.42    inference(superposition,[],[f126,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f35,f36])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    ( ! [X0] : (v1_subset_1(k6_domain_1(X0,sK1),sK0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0)) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f125])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    $false | spl2_3),
% 0.20/0.42    inference(resolution,[],[f123,f25])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    ~m1_subset_1(sK1,sK0) | spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f121])).
% 0.20/0.42  fof(f121,plain,(
% 0.20/0.42    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    spl2_2 | ~spl2_3 | spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f80,f125,f121,f46])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (v1_subset_1(k6_domain_1(X0,sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(superposition,[],[f26,f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k6_domain_1(X1,X0) = k6_domain_1(X2,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.20/0.42    inference(superposition,[],[f39,f39])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ~spl2_2),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    $false | ~spl2_2),
% 0.20/0.42    inference(resolution,[],[f48,f24])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f46])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_1 | spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f40,f46,f42])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | r2_hidden(sK1,sK0)),
% 0.20/0.42    inference(resolution,[],[f34,f25])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (3410)------------------------------
% 0.20/0.42  % (3410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (3410)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (3410)Memory used [KB]: 6140
% 0.20/0.42  % (3410)Time elapsed: 0.007 s
% 0.20/0.42  % (3410)------------------------------
% 0.20/0.42  % (3410)------------------------------
% 0.20/0.43  % (3405)Success in time 0.065 s
%------------------------------------------------------------------------------
