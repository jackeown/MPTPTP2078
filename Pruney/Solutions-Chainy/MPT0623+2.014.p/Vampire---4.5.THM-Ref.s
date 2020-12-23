%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 300 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  540 (1263 expanded)
%              Number of equality atoms :  208 ( 533 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f151,f156,f161,f180,f187,f194,f230,f245,f268,f278,f775])).

fof(f775,plain,
    ( spl9_1
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | spl9_1
    | ~ spl9_11 ),
    inference(trivial_inequality_removal,[],[f773])).

fof(f773,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl9_1
    | ~ spl9_11 ),
    inference(superposition,[],[f104,f554])).

fof(f554,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f548,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[],[f94,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f94,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f71,f72,f72])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f548,plain,
    ( ! [X25] : sK1 = k1_setfam_1(k2_tarski(k1_xboole_0,X25))
    | ~ spl9_11 ),
    inference(resolution,[],[f448,f285])).

fof(f285,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl9_11 ),
    inference(resolution,[],[f282,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f282,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X10,sK1)
        | ~ r2_hidden(X9,X10) )
    | ~ spl9_11 ),
    inference(resolution,[],[f244,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f244,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl9_11
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f448,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK8(X3,X4,sK1),X4)
        | sK1 = k1_setfam_1(k2_tarski(X4,X3)) )
    | ~ spl9_11 ),
    inference(resolution,[],[f445,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f92,f72])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f445,plain,
    ( ! [X30,X29] :
        ( sP0(X29,X30,sK1)
        | r2_hidden(sK8(X29,X30,sK1),X30) )
    | ~ spl9_11 ),
    inference(resolution,[],[f88,f244])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X0)
              & r2_hidden(sK8(X0,X1,X2),X1) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X0)
            & r2_hidden(sK8(X0,X1,X2),X1) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl9_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f278,plain,
    ( ~ spl9_2
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(trivial_inequality_removal,[],[f274])).

fof(f274,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(superposition,[],[f195,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f195,plain,
    ( k1_xboole_0 != sK2
    | ~ spl9_8 ),
    inference(equality_resolution,[],[f193])).

fof(f193,plain,
    ( ! [X0] :
        ( sK2 != X0
        | k1_xboole_0 != X0 )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl9_8
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | sK2 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f268,plain,
    ( ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(superposition,[],[f195,f246])).

fof(f246,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_10 ),
    inference(equality_resolution,[],[f229])).

fof(f229,plain,
    ( ! [X0] :
        ( sK2 != X0
        | k1_xboole_0 = X0 )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl9_10
  <=> ! [X0] :
        ( sK2 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f245,plain,
    ( spl9_11
    | spl9_10
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f241,f225,f228,f243])).

fof(f225,plain,
    ( spl9_9
  <=> ! [X1] : sK5(k1_tarski(X1),sK1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( sK2 != X0
        | ~ r2_hidden(X1,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( sK2 != X0
        | ~ r2_hidden(X1,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl9_9 ),
    inference(superposition,[],[f239,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK3(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK3(X0,X1))
          & k1_relat_1(sK3(X0,X1)) = X0
          & v1_funct_1(sK3(X0,X1))
          & v1_relat_1(sK3(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK3(X0,X1))
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f239,plain,
    ( ! [X0,X1] :
        ( sK2 != k1_relat_1(sK3(X1,X0))
        | ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = X1 )
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | sK2 != k1_relat_1(sK3(X1,X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X1 )
    | ~ spl9_9 ),
    inference(resolution,[],[f237,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK3(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3(X0,X1))
        | ~ r2_hidden(X1,sK1)
        | sK2 != k1_relat_1(sK3(X0,X1))
        | k1_xboole_0 = X0 )
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( sK2 != k1_relat_1(sK3(X0,X1))
        | ~ r2_hidden(X1,sK1)
        | ~ v1_relat_1(sK3(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl9_9 ),
    inference(resolution,[],[f235,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK3(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK3(X1,X0))
        | sK2 != k1_relat_1(sK3(X1,X0))
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl9_9 ),
    inference(resolution,[],[f233,f208])).

fof(f208,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK1)
      | sK2 != k1_relat_1(sK3(X4,X5))
      | ~ v1_funct_1(sK3(X4,X5))
      | ~ v1_relat_1(sK3(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f54,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK3(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK1)
      | k1_relat_1(X2) != sK2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK1)
        | k1_relat_1(X2) != sK2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK1 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK1)
          | k1_relat_1(X2) != sK2
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK1 ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f233,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_9 ),
    inference(superposition,[],[f76,f226])).

fof(f226,plain,
    ( ! [X1] : sK5(k1_tarski(X1),sK1) = X1
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f225])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f230,plain,
    ( spl9_9
    | spl9_10 ),
    inference(avatar_split_clause,[],[f223,f228,f225])).

fof(f223,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | sK5(k1_tarski(X1),sK1) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | sK5(k1_tarski(X1),sK1) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f221,f65])).

fof(f221,plain,(
    ! [X0,X1] :
      ( sK2 != k1_relat_1(sK3(X1,X0))
      | sK5(k1_tarski(X0),sK1) = X0
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( sK5(k1_tarski(X0),sK1) = X0
      | sK2 != k1_relat_1(sK3(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f219,f63])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3(X0,X1))
      | sK5(k1_tarski(X1),sK1) = X1
      | sK2 != k1_relat_1(sK3(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( sK2 != k1_relat_1(sK3(X0,X1))
      | sK5(k1_tarski(X1),sK1) = X1
      | ~ v1_relat_1(sK3(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f217,f64])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3(X1,X0))
      | sK2 != k1_relat_1(sK3(X1,X0))
      | sK5(k1_tarski(X0),sK1) = X0
      | ~ v1_relat_1(sK3(X1,X0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f114,f208])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f75,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f194,plain,
    ( ~ spl9_5
    | spl9_8
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f190,f178,f148,f192,f153])).

fof(f153,plain,
    ( spl9_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f148,plain,
    ( spl9_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f178,plain,
    ( spl9_7
  <=> ! [X1] :
        ( sK2 != X1
        | k1_xboole_0 != X1
        | ~ v1_relat_1(sK4(X1))
        | ~ v1_funct_1(sK4(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(k1_xboole_0)
        | sK2 != X0 )
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(k1_xboole_0)
        | sK2 != X0
        | k1_xboole_0 != X0 )
    | ~ spl9_7 ),
    inference(superposition,[],[f179,f138])).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f117,f69])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0))
      | k1_xboole_0 = sK4(X0) ) ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f179,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK4(X1))
        | k1_xboole_0 != X1
        | ~ v1_relat_1(sK4(X1))
        | sK2 != X1 )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f187,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl9_6 ),
    inference(resolution,[],[f176,f57])).

fof(f176,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl9_6
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f180,plain,
    ( ~ spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,(
    ! [X1] :
      ( sK2 != X1
      | ~ r1_tarski(k1_xboole_0,sK1)
      | ~ v1_funct_1(sK4(X1))
      | ~ v1_relat_1(sK4(X1))
      | k1_xboole_0 != X1 ) ),
    inference(forward_demodulation,[],[f169,f69])).

fof(f169,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,sK1)
      | sK2 != k1_relat_1(sK4(X1))
      | ~ v1_funct_1(sK4(X1))
      | ~ v1_relat_1(sK4(X1))
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f54,f163])).

fof(f163,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK4(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f157,f69])).

fof(f157,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0))
      | k1_xboole_0 = k2_relat_1(sK4(X0)) ) ),
    inference(resolution,[],[f61,f67])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f161,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl9_3 ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,
    ( ! [X4] : k1_xboole_0 != X4
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_3
  <=> ! [X4] : k1_xboole_0 != X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f156,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f143,f153,f145])).

fof(f143,plain,(
    ! [X5] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X5 ) ),
    inference(superposition,[],[f67,f138])).

fof(f151,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f142,f148,f145])).

fof(f142,plain,(
    ! [X4] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X4 ) ),
    inference(superposition,[],[f68,f138])).

fof(f68,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f53,f106,f102])).

fof(f53,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13955)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (13942)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13942)Refutation not found, incomplete strategy% (13942)------------------------------
% 0.21/0.51  % (13942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13950)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (13945)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (13947)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (13942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13942)Memory used [KB]: 10746
% 0.21/0.51  % (13942)Time elapsed: 0.103 s
% 0.21/0.51  % (13942)------------------------------
% 0.21/0.51  % (13942)------------------------------
% 0.21/0.51  % (13961)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (13950)Refutation not found, incomplete strategy% (13950)------------------------------
% 0.21/0.52  % (13950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13944)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13950)Memory used [KB]: 10618
% 0.21/0.52  % (13950)Time elapsed: 0.103 s
% 0.21/0.52  % (13950)------------------------------
% 0.21/0.52  % (13950)------------------------------
% 0.21/0.52  % (13941)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (13963)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (13967)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13952)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (13962)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (13966)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (13951)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13940)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (13940)Refutation not found, incomplete strategy% (13940)------------------------------
% 0.21/0.53  % (13940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13940)Memory used [KB]: 1663
% 0.21/0.53  % (13940)Time elapsed: 0.095 s
% 0.21/0.53  % (13940)------------------------------
% 0.21/0.53  % (13940)------------------------------
% 0.21/0.53  % (13949)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (13943)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (13949)Refutation not found, incomplete strategy% (13949)------------------------------
% 0.21/0.53  % (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13949)Memory used [KB]: 10618
% 0.21/0.53  % (13949)Time elapsed: 0.118 s
% 0.21/0.53  % (13949)------------------------------
% 0.21/0.53  % (13949)------------------------------
% 0.21/0.54  % (13954)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (13956)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13959)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (13968)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (13948)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (13948)Refutation not found, incomplete strategy% (13948)------------------------------
% 0.21/0.54  % (13948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13948)Memory used [KB]: 10746
% 0.21/0.54  % (13948)Time elapsed: 0.140 s
% 0.21/0.54  % (13948)------------------------------
% 0.21/0.54  % (13948)------------------------------
% 0.21/0.55  % (13946)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (13957)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (13960)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13957)Refutation not found, incomplete strategy% (13957)------------------------------
% 0.21/0.55  % (13957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13957)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13957)Memory used [KB]: 10618
% 0.21/0.55  % (13957)Time elapsed: 0.144 s
% 0.21/0.55  % (13957)------------------------------
% 0.21/0.55  % (13957)------------------------------
% 0.21/0.55  % (13965)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13958)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (13953)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (13964)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (13969)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (13952)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f776,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f109,f151,f156,f161,f180,f187,f194,f230,f245,f268,f278,f775])).
% 0.21/0.56  fof(f775,plain,(
% 0.21/0.56    spl9_1 | ~spl9_11),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f774])).
% 0.21/0.56  fof(f774,plain,(
% 0.21/0.56    $false | (spl9_1 | ~spl9_11)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f773])).
% 0.21/0.56  fof(f773,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | (spl9_1 | ~spl9_11)),
% 0.21/0.56    inference(superposition,[],[f104,f554])).
% 0.21/0.56  fof(f554,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~spl9_11),
% 0.21/0.56    inference(forward_demodulation,[],[f548,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.21/0.56    inference(superposition,[],[f94,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f58,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f71,f72,f72])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    ( ! [X25] : (sK1 = k1_setfam_1(k2_tarski(k1_xboole_0,X25))) ) | ~spl9_11),
% 0.21/0.56    inference(resolution,[],[f448,f285])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl9_11),
% 0.21/0.56    inference(resolution,[],[f282,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f282,plain,(
% 0.21/0.56    ( ! [X10,X9] : (~r1_tarski(X10,sK1) | ~r2_hidden(X9,X10)) ) | ~spl9_11),
% 0.21/0.56    inference(resolution,[],[f244,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f243])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    spl9_11 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.56  fof(f448,plain,(
% 0.21/0.56    ( ! [X4,X3] : (r2_hidden(sK8(X3,X4,sK1),X4) | sK1 = k1_setfam_1(k2_tarski(X4,X3))) ) | ~spl9_11),
% 0.21/0.56    inference(resolution,[],[f445,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f92,f72])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.56    inference(definition_folding,[],[f3,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.56  fof(f445,plain,(
% 0.21/0.56    ( ! [X30,X29] : (sP0(X29,X30,sK1) | r2_hidden(sK8(X29,X30,sK1),X30)) ) | ~spl9_11),
% 0.21/0.56    inference(resolution,[],[f88,f244])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X2) | r2_hidden(sK8(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X0) & r2_hidden(sK8(X0,X1,X2),X1)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.56    inference(flattening,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f28])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    spl9_1 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    ~spl9_2 | ~spl9_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f277])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    $false | (~spl9_2 | ~spl9_8)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f274])).
% 0.21/0.56  fof(f274,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | (~spl9_2 | ~spl9_8)),
% 0.21/0.56    inference(superposition,[],[f195,f108])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    spl9_2 <=> k1_xboole_0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    k1_xboole_0 != sK2 | ~spl9_8),
% 0.21/0.56    inference(equality_resolution,[],[f193])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    ( ! [X0] : (sK2 != X0 | k1_xboole_0 != X0) ) | ~spl9_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f192])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    spl9_8 <=> ! [X0] : (k1_xboole_0 != X0 | sK2 != X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.56  fof(f268,plain,(
% 0.21/0.56    ~spl9_8 | ~spl9_10),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    $false | (~spl9_8 | ~spl9_10)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f266])).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | (~spl9_8 | ~spl9_10)),
% 0.21/0.56    inference(superposition,[],[f195,f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl9_10),
% 0.21/0.56    inference(equality_resolution,[],[f229])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    ( ! [X0] : (sK2 != X0 | k1_xboole_0 = X0) ) | ~spl9_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f228])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    spl9_10 <=> ! [X0] : (sK2 != X0 | k1_xboole_0 = X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    spl9_11 | spl9_10 | ~spl9_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f241,f225,f228,f243])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    spl9_9 <=> ! [X1] : sK5(k1_tarski(X1),sK1) = X1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != X0 | ~r2_hidden(X1,sK1) | k1_xboole_0 = X0) ) | ~spl9_9),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f240])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != X0 | ~r2_hidden(X1,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl9_9),
% 0.21/0.56    inference(superposition,[],[f239,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK3(X0,X1)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK3(X0,X1)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != k1_relat_1(sK3(X1,X0)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = X1) ) | ~spl9_9),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f238])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | sK2 != k1_relat_1(sK3(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) ) | ~spl9_9),
% 0.21/0.56    inference(resolution,[],[f237,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(sK3(X0,X1)) | ~r2_hidden(X1,sK1) | sK2 != k1_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0) ) | ~spl9_9),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f236])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != k1_relat_1(sK3(X0,X1)) | ~r2_hidden(X1,sK1) | ~v1_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl9_9),
% 0.21/0.56    inference(resolution,[],[f235,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(sK3(X1,X0)) | sK2 != k1_relat_1(sK3(X1,X0)) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3(X1,X0)) | k1_xboole_0 = X1) ) | ~spl9_9),
% 0.21/0.56    inference(resolution,[],[f233,f208])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK1) | sK2 != k1_relat_1(sK3(X4,X5)) | ~v1_funct_1(sK3(X4,X5)) | ~v1_relat_1(sK3(X4,X5)) | k1_xboole_0 = X4) )),
% 0.21/0.56    inference(superposition,[],[f54,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK1) | k1_relat_1(X2) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK1) | k1_relat_1(X2) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK1)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK1) | k1_relat_1(X2) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.56    inference(negated_conjecture,[],[f15])).
% 0.21/0.56  fof(f15,conjecture,(
% 0.21/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK1) | ~r2_hidden(X0,sK1)) ) | ~spl9_9),
% 0.21/0.56    inference(superposition,[],[f76,f226])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ( ! [X1] : (sK5(k1_tarski(X1),sK1) = X1) ) | ~spl9_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f225])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f230,plain,(
% 0.21/0.56    spl9_9 | spl9_10),
% 0.21/0.56    inference(avatar_split_clause,[],[f223,f228,f225])).
% 0.21/0.56  fof(f223,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != X0 | sK5(k1_tarski(X1),sK1) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f222])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != X0 | sK5(k1_tarski(X1),sK1) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(superposition,[],[f221,f65])).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != k1_relat_1(sK3(X1,X0)) | sK5(k1_tarski(X0),sK1) = X0 | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK5(k1_tarski(X0),sK1) = X0 | sK2 != k1_relat_1(sK3(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f219,f63])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(sK3(X0,X1)) | sK5(k1_tarski(X1),sK1) = X1 | sK2 != k1_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f218])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2 != k1_relat_1(sK3(X0,X1)) | sK5(k1_tarski(X1),sK1) = X1 | ~v1_relat_1(sK3(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f217,f64])).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(sK3(X1,X0)) | sK2 != k1_relat_1(sK3(X1,X0)) | sK5(k1_tarski(X0),sK1) = X0 | ~v1_relat_1(sK3(X1,X0)) | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f114,f208])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 0.21/0.56    inference(resolution,[],[f75,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.56    inference(equality_resolution,[],[f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(rectify,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    ~spl9_5 | spl9_8 | ~spl9_4 | ~spl9_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f190,f178,f148,f192,f153])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    spl9_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    spl9_4 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    spl9_7 <=> ! [X1] : (sK2 != X1 | k1_xboole_0 != X1 | ~v1_relat_1(sK4(X1)) | ~v1_funct_1(sK4(X1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | k1_xboole_0 != X0 | ~v1_relat_1(k1_xboole_0) | sK2 != X0) ) | ~spl9_7),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | k1_xboole_0 != X0 | ~v1_relat_1(k1_xboole_0) | sK2 != X0 | k1_xboole_0 != X0) ) | ~spl9_7),
% 0.21/0.56    inference(superposition,[],[f179,f138])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK4(X0) | k1_xboole_0 != X0) )),
% 0.21/0.56    inference(superposition,[],[f117,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK4(X0)) | k1_xboole_0 = sK4(X0)) )),
% 0.21/0.56    inference(resolution,[],[f59,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X1] : (~v1_funct_1(sK4(X1)) | k1_xboole_0 != X1 | ~v1_relat_1(sK4(X1)) | sK2 != X1) ) | ~spl9_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f178])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    spl9_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    $false | spl9_6),
% 0.21/0.56    inference(resolution,[],[f176,f57])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK1) | spl9_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f174])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    spl9_6 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    ~spl9_6 | spl9_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f172,f178,f174])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ( ! [X1] : (sK2 != X1 | ~r1_tarski(k1_xboole_0,sK1) | ~v1_funct_1(sK4(X1)) | ~v1_relat_1(sK4(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.56    inference(forward_demodulation,[],[f169,f69])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK1) | sK2 != k1_relat_1(sK4(X1)) | ~v1_funct_1(sK4(X1)) | ~v1_relat_1(sK4(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.56    inference(superposition,[],[f54,f163])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK4(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f157,f69])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK4(X0)) | k1_xboole_0 = k2_relat_1(sK4(X0))) )),
% 0.21/0.56    inference(resolution,[],[f61,f67])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    ~spl9_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    $false | ~spl9_3),
% 0.21/0.56    inference(equality_resolution,[],[f146])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    ( ! [X4] : (k1_xboole_0 != X4) ) | ~spl9_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f145])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    spl9_3 <=> ! [X4] : k1_xboole_0 != X4),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    spl9_3 | spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f143,f153,f145])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ( ! [X5] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X5) )),
% 0.21/0.56    inference(superposition,[],[f67,f138])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    spl9_3 | spl9_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f142,f148,f145])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ( ! [X4] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X4) )),
% 0.21/0.56    inference(superposition,[],[f68,f138])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ~spl9_1 | spl9_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f53,f106,f102])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (13952)------------------------------
% 0.21/0.56  % (13952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13952)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (13952)Memory used [KB]: 6524
% 0.21/0.56  % (13952)Time elapsed: 0.152 s
% 0.21/0.56  % (13952)------------------------------
% 0.21/0.56  % (13952)------------------------------
% 0.21/0.56  % (13939)Success in time 0.196 s
%------------------------------------------------------------------------------
