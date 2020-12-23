%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0897+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 162 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 767 expanded)
%              Number of equality atoms :  165 ( 676 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f103,f109,f115,f148])).

fof(f148,plain,(
    ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl9_9 ),
    inference(global_subsumption,[],[f19,f126,f127,f128,f129])).

fof(f129,plain,
    ( sK1 = sK5
    | ~ spl9_9 ),
    inference(resolution,[],[f124,f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X6 = X7 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X0 = X1
        & X2 = X3
        & X4 = X5
        & X6 = X7 )
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X7,X3,X6,X2,X5,X1,X4,X0] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | ~ sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X7,X3,X6,X2,X5,X1,X4,X0] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | ~ sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f124,plain,
    ( sP0(sK4,sK8,sK3,sK7,sK2,sK6,sK1,sK5)
    | ~ spl9_9 ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK1,sK2,sK3,sK4) != k4_zfmisc_1(X28,X29,X30,X31)
        | sP0(X31,sK8,X30,sK7,X29,sK6,X28,sK5) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_9
  <=> ! [X29,X31,X28,X30] :
        ( k4_zfmisc_1(sK1,sK2,sK3,sK4) != k4_zfmisc_1(X28,X29,X30,X31)
        | sP0(X31,sK8,X30,sK7,X29,sK6,X28,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f128,plain,
    ( sK2 = sK6
    | ~ spl9_9 ),
    inference(resolution,[],[f124,f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,
    ( sK3 = sK7
    | ~ spl9_9 ),
    inference(resolution,[],[f124,f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,
    ( sK4 = sK8
    | ~ spl9_9 ),
    inference(resolution,[],[f124,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,
    ( sK4 != sK8
    | sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK4 != sK8
      | sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5 )
    & k1_xboole_0 != k4_zfmisc_1(sK1,sK2,sK3,sK4)
    & k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,sK6,sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK4 != sK8
        | sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5 )
      & k1_xboole_0 != k4_zfmisc_1(sK1,sK2,sK3,sK4)
      & k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f115,plain,(
    ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f113,f18])).

fof(f18,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f113,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK1,sK2,sK3,sK4)
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f111,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f111,plain,
    ( k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,sK6,sK7,k1_xboole_0)
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f17,f86])).

fof(f86,plain,
    ( k1_xboole_0 = sK8
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_8
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f17,plain,(
    k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f107,f18])).

fof(f107,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK1,sK2,sK3,sK4)
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f105,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,sK6,k1_xboole_0,sK8)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f17,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl9_7
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f103,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f101,f18])).

fof(f101,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK1,sK2,sK3,sK4)
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f99,f32])).

fof(f32,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(sK5,k1_xboole_0,sK7,sK8)
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f17,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl9_6
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f97,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f95,f18])).

fof(f95,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK1,sK2,sK3,sK4)
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f93,f33])).

fof(f33,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,
    ( k4_zfmisc_1(sK1,sK2,sK3,sK4) = k4_zfmisc_1(k1_xboole_0,sK6,sK7,sK8)
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f17,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl9_5
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f90,plain,
    ( spl9_5
    | spl9_6
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f60,f88,f84,f80,f76,f72])).

fof(f60,plain,(
    ! [X30,X28,X31,X29] :
      ( k4_zfmisc_1(sK1,sK2,sK3,sK4) != k4_zfmisc_1(X28,X29,X30,X31)
      | k1_xboole_0 = sK8
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | sP0(X31,sK8,X30,sK7,X29,sK6,X28,sK5) ) ),
    inference(superposition,[],[f29,f17])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP0(X7,X3,X6,X2,X5,X1,X4,X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f8,f9])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

%------------------------------------------------------------------------------
