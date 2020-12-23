%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 134 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 350 expanded)
%              Number of equality atoms :   30 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f98,f105,f118,f147])).

fof(f147,plain,
    ( ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f138,f122])).

fof(f122,plain,
    ( k1_xboole_0 != k6_domain_1(sK0,sK1)
    | ~ spl2_8 ),
    inference(superposition,[],[f90,f104])).

fof(f104,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_8
  <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f37,f43,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f138,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f117,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_4 ),
    inference(resolution,[],[f42,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f117,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_9
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f118,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f99,f95,f70,f55,f115])).

fof(f55,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( spl2_5
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f95,plain,
    ( spl2_7
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f57,f72,f97,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f97,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f72,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f57,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f105,plain,
    ( spl2_8
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f91,f60,f50,f102])).

fof(f50,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f91,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f52,f62,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f62,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f52,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f98,plain,
    ( spl2_7
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f80,f60,f50,f95])).

fof(f80,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f52,f62,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f73,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f68,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (21379)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (21392)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (21392)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f98,f105,f118,f147])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~spl2_4 | ~spl2_8 | ~spl2_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    $false | (~spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f138,f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    k1_xboole_0 != k6_domain_1(sK0,sK1) | ~spl2_8),
% 0.21/0.46    inference(superposition,[],[f90,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl2_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f102])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    spl2_8 <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.21/0.46    inference(superposition,[],[f46,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f36,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f38,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f37,f43,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f33,f39])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    k1_xboole_0 = k6_domain_1(sK0,sK1) | (~spl2_4 | ~spl2_9)),
% 0.21/0.46    inference(resolution,[],[f117,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_4),
% 0.21/0.46    inference(resolution,[],[f42,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl2_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl2_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl2_9 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl2_9 | ~spl2_2 | ~spl2_5 | ~spl2_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f99,f95,f70,f55,f115])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl2_5 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl2_7 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl2_2 | ~spl2_5 | ~spl2_7)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f57,f72,f97,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f35,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f70])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    spl2_8 | spl2_1 | ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f91,f60,f50,f102])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | (spl2_1 | ~spl2_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f62,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f40,f44])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~v1_xboole_0(sK0) | spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl2_7 | spl2_1 | ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f80,f60,f50,f95])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f62,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f70])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.46    inference(negated_conjecture,[],[f12])).
% 0.21/0.46  fof(f12,conjecture,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f65])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f60])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    m1_subset_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f55])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v1_zfmisc_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f50])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~v1_xboole_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21392)------------------------------
% 0.21/0.46  % (21392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21392)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21392)Memory used [KB]: 10618
% 0.21/0.46  % (21392)Time elapsed: 0.031 s
% 0.21/0.46  % (21392)------------------------------
% 0.21/0.46  % (21392)------------------------------
% 0.21/0.47  % (21376)Success in time 0.108 s
%------------------------------------------------------------------------------
