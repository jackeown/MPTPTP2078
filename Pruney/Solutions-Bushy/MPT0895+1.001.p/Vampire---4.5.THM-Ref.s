%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 169 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 714 expanded)
%              Number of equality atoms :  186 ( 607 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f56,f58,f60,f62,f67,f72,f77,f81,f87,f91])).

fof(f91,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f90,f85,f45,f42,f39])).

fof(f39,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f42,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f45,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( spl4_6
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(superposition,[],[f23,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f87,plain,
    ( spl4_4
    | spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f83,f51,f85,f48])).

fof(f48,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f51,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(superposition,[],[f20,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl4_4
    | spl4_5 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4
    | spl4_5 ),
    inference(superposition,[],[f78,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f55,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,
    ( ~ spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl4_3
    | spl4_5 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_3
    | spl4_5 ),
    inference(superposition,[],[f74,f34])).

fof(f34,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f73,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f55,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f72,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_1
    | spl4_5 ),
    inference(superposition,[],[f69,f34])).

fof(f69,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f68,f37])).

fof(f37,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3)
    | ~ spl4_1
    | spl4_5 ),
    inference(forward_demodulation,[],[f55,f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f67,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_2
    | spl4_5 ),
    inference(superposition,[],[f64,f34])).

fof(f64,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(forward_demodulation,[],[f63,f36])).

fof(f36,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(forward_demodulation,[],[f55,f43])).

fof(f43,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f62,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f32,f51,f39])).

fof(f32,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f15,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f15,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f60,plain,
    ( ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f31,f51,f42])).

fof(f31,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f16,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,
    ( ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f30,f51,f45])).

fof(f30,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f17,f27])).

fof(f17,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f29,f51,f48])).

fof(f29,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f18,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f28,f51,f48,f45,f42,f39])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f19,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
