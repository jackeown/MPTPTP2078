%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0878+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:49 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  78 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 230 expanded)
%              Number of equality atoms :   74 ( 177 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f42,f60])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f54,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f14,f26])).

fof(f26,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK1 != sK2
    & k3_zfmisc_1(sK1,sK1,sK1) = k3_zfmisc_1(sK2,sK2,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f4,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK1 != sK2
      & k3_zfmisc_1(sK1,sK1,sK1) = k3_zfmisc_1(sK2,sK2,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X0 = X1
        & X2 = X3
        & X4 = X5 )
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X5,X2,X4,X1,X3,X0] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | ~ sP0(X5,X2,X4,X1,X3,X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X5,X2,X4,X1,X3,X0] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | ~ sP0(X5,X2,X4,X1,X3,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f50,plain,
    ( sP0(k1_xboole_0,sK1,k1_xboole_0,sK1,k1_xboole_0,sK1)
    | ~ spl3_1 ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
        | sP0(X5,sK1,X4,sK1,X3,sK1) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f47,f44])).

fof(f47,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
        | k1_xboole_0 = sK1
        | sP0(X5,sK1,X4,sK1,X3,sK1) )
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | sP0(X5,sK1,X4,sK1,X3,sK1) )
    | ~ spl3_1 ),
    inference(superposition,[],[f18,f43])).

fof(f43,plain,
    ( k3_zfmisc_1(sK1,sK1,sK1) = k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f13,f26])).

fof(f13,plain,(
    k3_zfmisc_1(sK1,sK1,sK1) = k3_zfmisc_1(sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sP0(X5,X2,X4,X1,X3,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP0(X5,X2,X4,X1,X3,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(definition_folding,[],[f6,f7])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f42,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f36,f14])).

fof(f36,plain,
    ( sK1 = sK2
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f15])).

fof(f32,plain,
    ( sP0(sK1,sK2,sK1,sK2,sK1,sK2)
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK1,sK1)
        | sP0(X2,sK2,X1,sK2,X0,sK2) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_2
  <=> ! [X1,X0,X2] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK1,sK1)
        | sP0(X2,sK2,X1,sK2,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f22,f28,f24])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK1,sK1)
      | k1_xboole_0 = sK2
      | sP0(X2,sK2,X1,sK2,X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK1,sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | sP0(X2,sK2,X1,sK2,X0,sK2) ) ),
    inference(superposition,[],[f18,f13])).

%------------------------------------------------------------------------------
