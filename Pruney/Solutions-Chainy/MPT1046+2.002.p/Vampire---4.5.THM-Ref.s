%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 143 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 ( 402 expanded)
%              Number of equality atoms :   62 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f95,f100,f124,f132,f140,f144,f152,f154])).

fof(f154,plain,
    ( k1_xboole_0 != sK0
    | sK1 != k3_partfun1(sK1,sK0,sK0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,sK1)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f152,plain,
    ( ~ spl2_4
    | ~ spl2_14
    | spl2_16
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f146,f142,f126,f150,f138,f67])).

fof(f67,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f138,plain,
    ( spl2_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f150,plain,
    ( spl2_16
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f126,plain,
    ( spl2_12
  <=> sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f142,plain,
    ( spl2_15
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f146,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f145,f127])).

fof(f127,plain,
    ( sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_1(sK1)
    | ~ spl2_15 ),
    inference(resolution,[],[f143,f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k2_enumset1(X2,X2,X2,X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k2_enumset1(X2,X2,X2,X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f41,f45])).

% (16606)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f143,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f131,f121,f63,f142])).

fof(f63,plain,
    ( spl2_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f121,plain,
    ( spl2_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f131,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(superposition,[],[f64,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f64,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f140,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f130,f121,f59,f138])).

fof(f59,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f60,f122])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f132,plain,
    ( spl2_12
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f128,f121,f93,f126])).

fof(f93,plain,
    ( spl2_9
  <=> sK1 = k3_partfun1(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f128,plain,
    ( sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(superposition,[],[f94,f122])).

fof(f94,plain,
    ( sK1 = k3_partfun1(sK1,sK0,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f124,plain,
    ( ~ spl2_3
    | spl2_11
    | spl2_10
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f118,f93,f67,f59,f98,f121,f63])).

fof(f98,plain,
    ( spl2_10
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f118,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f117,f94])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f60])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,X1,X0)
        | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k2_enumset1(X2,X2,X2,X2) ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f96,f93,f55,f98])).

fof(f55,plain,
    ( spl2_1
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f96,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != k5_partfun1(sK0,sK0,sK1)
    | spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f56,f94])).

fof(f56,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f95,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f91,f67,f59,f93])).

fof(f91,plain,
    ( sK1 = k3_partfun1(sK1,sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK1 = k3_partfun1(sK1,X0,X1) )
    | ~ spl2_4 ),
    inference(resolution,[],[f42,f68])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f65,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f46,f55])).

fof(f46,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f30,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (16598)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % (16608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (16620)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.50  % (16611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.50  % (16611)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f95,f100,f124,f132,f140,f144,f152,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | sK1 != k3_partfun1(sK1,sK0,sK0) | k2_enumset1(sK1,sK1,sK1,sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,sK1) | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ~spl2_4 | ~spl2_14 | spl2_16 | ~spl2_12 | ~spl2_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f146,f142,f126,f150,f138,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl2_4 <=> v1_funct_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl2_14 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl2_16 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl2_12 <=> sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl2_15 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | (~spl2_12 | ~spl2_15)),
% 0.22/0.50    inference(forward_demodulation,[],[f145,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f126])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(sK1) | ~spl2_15),
% 0.22/0.50    inference(resolution,[],[f143,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k2_enumset1(X2,X2,X2,X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k2_enumset1(X2,X2,X2,X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f41,f45])).
% 0.22/0.50  % (16606)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f34,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl2_15 | ~spl2_3 | ~spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f121,f63,f142])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl2_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl2_11 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_11)),
% 0.22/0.50    inference(superposition,[],[f64,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl2_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    v1_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl2_14 | ~spl2_2 | ~spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f130,f121,f59,f138])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_2 | ~spl2_11)),
% 0.22/0.50    inference(superposition,[],[f60,f122])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl2_12 | ~spl2_9 | ~spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f121,f93,f126])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl2_9 <=> sK1 = k3_partfun1(sK1,sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    sK1 = k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_9 | ~spl2_11)),
% 0.22/0.50    inference(superposition,[],[f94,f122])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    sK1 = k3_partfun1(sK1,sK0,sK0) | ~spl2_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~spl2_3 | spl2_11 | spl2_10 | ~spl2_2 | ~spl2_4 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f118,f93,f67,f59,f98,f121,f63])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl2_10 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | (~spl2_2 | ~spl2_4 | ~spl2_9)),
% 0.22/0.50    inference(forward_demodulation,[],[f117,f94])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(resolution,[],[f116,f60])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,X1,X0) | k2_enumset1(sK1,sK1,sK1,sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0))) ) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f50,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    v1_funct_1(sK1) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k2_enumset1(X2,X2,X2,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f40,f45])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ~spl2_10 | spl2_1 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f93,f55,f98])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl2_1 <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k2_enumset1(sK1,sK1,sK1,sK1) != k5_partfun1(sK0,sK0,sK1) | (spl2_1 | ~spl2_9)),
% 0.22/0.50    inference(superposition,[],[f56,f94])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k2_enumset1(sK1,sK1,sK1,sK1) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl2_9 | ~spl2_2 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f91,f67,f59,f93])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    sK1 = k3_partfun1(sK1,sK0,sK0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.50    inference(resolution,[],[f90,f60])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k3_partfun1(sK1,X0,X1)) ) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f42,f68])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    v1_funct_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f63])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f59])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f55])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f45])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (16611)------------------------------
% 0.22/0.50  % (16611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16611)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (16611)Memory used [KB]: 10746
% 0.22/0.50  % (16611)Time elapsed: 0.093 s
% 0.22/0.50  % (16611)------------------------------
% 0.22/0.50  % (16611)------------------------------
% 0.22/0.50  % (16591)Success in time 0.139 s
%------------------------------------------------------------------------------
