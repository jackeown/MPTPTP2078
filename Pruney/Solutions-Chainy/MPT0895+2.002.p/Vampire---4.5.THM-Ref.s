%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 185 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 ( 766 expanded)
%              Number of equality atoms :  159 ( 643 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f65,f66,f67,f68,f73,f78,f82,f85,f102])).

fof(f102,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f21,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f95,f54])).

fof(f54,plain,
    ( k1_xboole_0 != sK2
    | spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f95,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | spl4_4
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f21,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK3
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(superposition,[],[f21,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f85,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f62,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f62,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f82,plain,
    ( ~ spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f79,f39])).

fof(f79,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f62,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f78,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f75,f40])).

fof(f75,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f74,f40])).

fof(f74,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3)
    | ~ spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f62,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f73,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f71,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f70,f40])).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f69,f39])).

fof(f69,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(forward_demodulation,[],[f62,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f68,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f34,f61,f45])).

fof(f34,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f16,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f16,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f67,plain,
    ( ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f33,f61,f49])).

fof(f33,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f17,f29])).

fof(f17,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f32,f61,f53])).

fof(f32,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f18,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f31,f61,f57])).

fof(f31,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f19,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f30,f61,f57,f53,f49,f45])).

fof(f30,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f20,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:15:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (10336)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (10347)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (10336)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f64,f65,f66,f67,f68,f73,f78,f82,f85,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl4_1 | spl4_2 | spl4_3 | spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    $false | (spl4_1 | spl4_2 | spl4_3 | spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f100,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (spl4_1 | spl4_3 | spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f99,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl4_1 <=> k1_xboole_0 = sK0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (spl4_3 | spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (spl4_3 | spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(superposition,[],[f21,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl4_3 | spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f95,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl4_3 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | (spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | (spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(superposition,[],[f21,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k1_xboole_0 != sK3 | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_4 <=> k1_xboole_0 = sK3),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl4_5),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl4_5),
% 0.22/0.53    inference(superposition,[],[f21,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~spl4_4 | spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    $false | (~spl4_4 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f83,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | (~spl4_4 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    k1_xboole_0 = sK3 | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ~spl4_3 | spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    $false | (~spl4_3 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f80,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_3 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f79,f39])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3) | (~spl4_3 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~spl4_1 | spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    $false | (~spl4_1 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f76,f40])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_1 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f75,f40])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (~spl4_1 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f74,f40])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3) | (~spl4_1 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f45])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~spl4_2 | spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    $false | (~spl4_2 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f71,f40])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_2 | spl4_5)),
% 0.22/0.53    inference(backward_demodulation,[],[f70,f40])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (~spl4_2 | spl4_5)),
% 0.22/0.53    inference(backward_demodulation,[],[f69,f39])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3) | (~spl4_2 | spl4_5)),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f61,f45])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK0),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    (k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))) => ((k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~spl4_2 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f61,f49])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK1),
% 0.22/0.53    inference(definition_unfolding,[],[f17,f29])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ~spl4_3 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f61,f53])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK2),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f29])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f61,f57])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK3),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f29])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK3),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl4_1 | spl4_2 | spl4_3 | spl4_4 | spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f61,f57,f53,f49,f45])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(definition_unfolding,[],[f20,f29])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10336)------------------------------
% 0.22/0.53  % (10336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10336)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10336)Memory used [KB]: 10746
% 0.22/0.53  % (10336)Time elapsed: 0.102 s
% 0.22/0.53  % (10336)------------------------------
% 0.22/0.53  % (10336)------------------------------
% 0.22/0.53  % (10332)Success in time 0.16 s
%------------------------------------------------------------------------------
