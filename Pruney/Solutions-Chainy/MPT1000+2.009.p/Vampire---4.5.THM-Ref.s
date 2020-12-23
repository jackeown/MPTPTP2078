%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 ( 431 expanded)
%              Number of equality atoms :   74 ( 159 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f53,f58,f63,f78,f105,f126,f133,f233])).

fof(f233,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f231,f39])).

fof(f39,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f231,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f230,f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f230,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f131,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f131,plain,
    ( sP0(sK3,sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_12
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f133,plain,
    ( spl6_12
    | ~ spl6_5
    | ~ spl6_7
    | spl6_11 ),
    inference(avatar_split_clause,[],[f110,f102,f74,f60,f129])).

fof(f60,plain,
    ( spl6_5
  <=> v1_funct_2(sK5,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f74,plain,
    ( spl6_7
  <=> sP1(sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f102,plain,
    ( spl6_11
  <=> sK3 = k1_relset_1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f110,plain,
    ( sP0(sK3,sK4)
    | ~ spl6_5
    | ~ spl6_7
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f76,f62,f104,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f104,plain,
    ( sK3 != k1_relset_1(sK3,sK4,sK5)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f62,plain,
    ( v1_funct_2(sK5,sK3,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f76,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f126,plain,
    ( spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | spl6_11 ),
    inference(subsumption_resolution,[],[f124,f76])).

fof(f124,plain,
    ( ~ sP1(sK3,sK5,sK4)
    | spl6_2
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f123,f69])).

fof(f69,plain,
    ( ! [X0] : ~ sP0(X0,sK4)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,
    ( k1_xboole_0 != sK4
    | spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f123,plain,
    ( sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f113,f62])).

fof(f113,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | spl6_11 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( sK3 != sK3
    | ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | spl6_11 ),
    inference(superposition,[],[f104,f30])).

fof(f105,plain,
    ( ~ spl6_11
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f100,f55,f41,f102])).

fof(f41,plain,
    ( spl6_1
  <=> sK3 = k8_relset_1(sK3,sK4,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f55,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f100,plain,
    ( sK3 != k1_relset_1(sK3,sK4,sK5)
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f57,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f94,plain,
    ( sK3 != k1_relset_1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | spl6_1 ),
    inference(superposition,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f43,plain,
    ( sK3 != k8_relset_1(sK3,sK4,sK5,sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f78,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f72,f55,f74])).

fof(f72,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl6_4 ),
    inference(resolution,[],[f34,f57])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f9,f12,f11,f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f63,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK3 != k8_relset_1(sK3,sK4,sK5,sK4)
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,X1) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK3 != k8_relset_1(sK3,sK4,sK5,sK4)
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f58,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f24,f50,f46])).

fof(f24,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    sK3 != k8_relset_1(sK3,sK4,sK5,sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (4367)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.42  % (4367)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f234,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f44,f53,f58,f63,f78,f105,f126,f133,f233])).
% 0.21/0.42  fof(f233,plain,(
% 0.21/0.42    ~spl6_2 | ~spl6_3 | ~spl6_12),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f232])).
% 0.21/0.42  fof(f232,plain,(
% 0.21/0.42    $false | (~spl6_2 | ~spl6_3 | ~spl6_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f231,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.42    inference(equality_resolution,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.42  fof(f231,plain,(
% 0.21/0.42    sP0(k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_3 | ~spl6_12)),
% 0.21/0.42    inference(forward_demodulation,[],[f230,f52])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    k1_xboole_0 = sK3 | ~spl6_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl6_3 <=> k1_xboole_0 = sK3),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.42  fof(f230,plain,(
% 0.21/0.42    sP0(sK3,k1_xboole_0) | (~spl6_2 | ~spl6_12)),
% 0.21/0.42    inference(forward_demodulation,[],[f131,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    k1_xboole_0 = sK4 | ~spl6_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl6_2 <=> k1_xboole_0 = sK4),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    sP0(sK3,sK4) | ~spl6_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f129])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    spl6_12 <=> sP0(sK3,sK4)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    spl6_12 | ~spl6_5 | ~spl6_7 | spl6_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f110,f102,f74,f60,f129])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl6_5 <=> v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl6_7 <=> sP1(sK3,sK5,sK4)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl6_11 <=> sK3 = k1_relset_1(sK3,sK4,sK5)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    sP0(sK3,sK4) | (~spl6_5 | ~spl6_7 | spl6_11)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f76,f62,f104,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.42    inference(rectify,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.42    inference(nnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    sK3 != k1_relset_1(sK3,sK4,sK5) | spl6_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f102])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    v1_funct_2(sK5,sK3,sK4) | ~spl6_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    sP1(sK3,sK5,sK4) | ~spl6_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl6_2 | ~spl6_5 | ~spl6_7 | spl6_11),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    $false | (spl6_2 | ~spl6_5 | ~spl6_7 | spl6_11)),
% 0.21/0.42    inference(subsumption_resolution,[],[f124,f76])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    ~sP1(sK3,sK5,sK4) | (spl6_2 | ~spl6_5 | spl6_11)),
% 0.21/0.42    inference(subsumption_resolution,[],[f123,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (~sP0(X0,sK4)) ) | spl6_2),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f48,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    k1_xboole_0 != sK4 | spl6_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | (~spl6_5 | spl6_11)),
% 0.21/0.42    inference(subsumption_resolution,[],[f113,f62])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | spl6_11),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f112])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    sK3 != sK3 | ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | spl6_11),
% 0.21/0.42    inference(superposition,[],[f104,f30])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ~spl6_11 | spl6_1 | ~spl6_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f100,f55,f41,f102])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl6_1 <=> sK3 = k8_relset_1(sK3,sK4,sK5,sK4)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl6_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    sK3 != k1_relset_1(sK3,sK4,sK5) | (spl6_1 | ~spl6_4)),
% 0.21/0.42    inference(subsumption_resolution,[],[f94,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl6_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    sK3 != k1_relset_1(sK3,sK4,sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | spl6_1),
% 0.21/0.42    inference(superposition,[],[f43,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    sK3 != k8_relset_1(sK3,sK4,sK5,sK4) | spl6_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl6_7 | ~spl6_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f72,f55,f74])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    sP1(sK3,sK5,sK4) | ~spl6_4),
% 0.21/0.42    inference(resolution,[],[f34,f57])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(definition_folding,[],[f9,f12,f11,f10])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl6_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f60])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    sK3 != k8_relset_1(sK3,sK4,sK5,sK4) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK3 != k8_relset_1(sK3,sK4,sK5,sK4) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl6_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f55])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ~spl6_2 | spl6_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f50,f46])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ~spl6_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f41])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    sK3 != k8_relset_1(sK3,sK4,sK5,sK4)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (4367)------------------------------
% 0.21/0.42  % (4367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (4367)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (4367)Memory used [KB]: 10746
% 0.21/0.42  % (4367)Time elapsed: 0.007 s
% 0.21/0.42  % (4367)------------------------------
% 0.21/0.42  % (4367)------------------------------
% 0.21/0.42  % (4350)Success in time 0.071 s
%------------------------------------------------------------------------------
