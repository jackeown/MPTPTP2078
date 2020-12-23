%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 169 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  227 ( 517 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f140,f160,f162,f170,f174,f185,f188,f190])).

fof(f190,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f94,f24])).

fof(f24,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f94,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f188,plain,(
    ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl2_8 ),
    inference(resolution,[],[f159,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f159,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_8
  <=> v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f185,plain,
    ( spl2_4
    | spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f178,f100,f132,f129])).

fof(f129,plain,
    ( spl2_4
  <=> ! [X4] :
        ( v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f132,plain,
    ( spl2_5
  <=> v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( spl2_3
  <=> ! [X0] :
        ( v1_subset_1(k6_domain_1(X0,sK1),sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f178,plain,
    ( ! [X4] :
        ( v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4) )
    | ~ spl2_3 ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( ! [X4] :
        ( v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK1,X4)
        | ~ m1_subset_1(sK1,X4)
        | v1_xboole_0(X4) )
    | ~ spl2_3 ),
    inference(superposition,[],[f101,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f35,f38])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f101,plain,
    ( ! [X0] :
        ( v1_subset_1(k6_domain_1(X0,sK1),sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK1,X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f174,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f172,f100,f96,f92])).

fof(f96,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f172,plain,(
    ! [X1] :
      ( v1_subset_1(k6_domain_1(X1,sK1),sK0)
      | ~ m1_subset_1(sK1,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f26,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X1,X0) = k6_domain_1(X2,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f40,f40])).

fof(f26,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f170,plain,(
    ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl2_7 ),
    inference(resolution,[],[f163,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f24,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f162,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f151,f27])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f151,plain,
    ( ~ v1_zfmisc_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl2_6
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f160,plain,
    ( spl2_1
    | ~ spl2_6
    | spl2_7
    | spl2_8
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f147,f132,f96,f157,f153,f149,f92])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK0
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_5 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK0
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f45,f134])).

fof(f134,plain,
    ( v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_subset_1(k2_enumset1(X4,X3,X2,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | v1_xboole_0(k2_enumset1(X4,X3,X2,X1))
      | k1_xboole_0 = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).

fof(f140,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl2_4 ),
    inference(resolution,[],[f136,f24])).

fof(f136,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f130,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK1,X4)
        | v1_xboole_0(X4) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f105,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f98,f25])).

fof(f98,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:51:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.47  % (31045)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (31045)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f105,f140,f160,f162,f170,f174,f185,f188,f190])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    $false | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f94,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    $false | ~spl2_8),
% 0.21/0.47    inference(resolution,[],[f159,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f29,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f33,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f157])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    spl2_8 <=> v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    spl2_4 | spl2_5 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f178,f100,f132,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl2_4 <=> ! [X4] : (v1_xboole_0(X4) | ~m1_subset_1(sK1,X4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl2_5 <=> v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl2_3 <=> ! [X0] : (v1_subset_1(k6_domain_1(X0,sK1),sK0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X4] : (v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | v1_xboole_0(X4) | ~m1_subset_1(sK1,X4)) ) | ~spl2_3),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ( ! [X4] : (v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | v1_xboole_0(X4) | ~m1_subset_1(sK1,X4) | ~m1_subset_1(sK1,X4) | v1_xboole_0(X4)) ) | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f101,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f35,f38])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0] : (v1_subset_1(k6_domain_1(X0,sK1),sK0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0)) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    spl2_1 | ~spl2_2 | spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f100,f96,f92])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl2_2 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X1] : (v1_subset_1(k6_domain_1(X1,sK1),sK0) | ~m1_subset_1(sK1,X1) | v1_xboole_0(X1) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.47    inference(superposition,[],[f26,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k6_domain_1(X1,X0) = k6_domain_1(X2,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(superposition,[],[f40,f40])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ~spl2_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    $false | ~spl2_7),
% 0.21/0.47    inference(resolution,[],[f163,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl2_7),
% 0.21/0.47    inference(backward_demodulation,[],[f24,f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl2_7 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    $false | spl2_6),
% 0.21/0.47    inference(resolution,[],[f151,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_zfmisc_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~v1_zfmisc_1(sK0) | spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl2_6 <=> v1_zfmisc_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl2_1 | ~spl2_6 | spl2_7 | spl2_8 | ~spl2_2 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f132,f96,f157,f153,f149,f92])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0 | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | ~spl2_5),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0 | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | ~spl2_5),
% 0.21/0.47    inference(resolution,[],[f45,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_subset_1(k2_enumset1(X4,X3,X2,X1),X0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X4,X0) | v1_xboole_0(k2_enumset1(X4,X3,X2,X1)) | k1_xboole_0 = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f34,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~spl2_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    $false | ~spl2_4),
% 0.21/0.48    inference(resolution,[],[f136,f24])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~spl2_4),
% 0.21/0.48    inference(resolution,[],[f130,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_subset_1(sK1,X4) | v1_xboole_0(X4)) ) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    $false | spl2_2),
% 0.21/0.48    inference(resolution,[],[f98,f25])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31045)------------------------------
% 0.21/0.48  % (31045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31045)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31045)Memory used [KB]: 6140
% 0.21/0.48  % (31045)Time elapsed: 0.037 s
% 0.21/0.48  % (31045)------------------------------
% 0.21/0.48  % (31045)------------------------------
% 0.21/0.48  % (31040)Success in time 0.11 s
%------------------------------------------------------------------------------
