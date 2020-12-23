%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 213 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  389 ( 955 expanded)
%              Number of equality atoms :  171 ( 431 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f83,f85,f135,f156,f166,f186,f210])).

fof(f210,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl7_1
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_1
    | ~ spl7_9 ),
    inference(superposition,[],[f61,f188])).

fof(f188,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(resolution,[],[f185,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f185,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_9
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f186,plain,
    ( spl7_9
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f182,f133,f118,f184])).

fof(f118,plain,
    ( spl7_7
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f133,plain,
    ( spl7_8
  <=> ! [X1] : sK4(k1_tarski(X1),sK0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(superposition,[],[f180,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f180,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f178,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2(X0,X1))
        | sK1 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X0,X1))
        | ~ v1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f174,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2(X0,X1))
        | sK1 != k1_relat_1(sK2(X0,X1))
        | ~ v1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f102,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_8 ),
    inference(superposition,[],[f46,f134])).

fof(f134,plain,
    ( ! [X1] : sK4(k1_tarski(X1),sK0) = X1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f102,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_funct_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f166,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f91,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_3 ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK6(X0,X1))
        | k1_xboole_0 != X0
        | sK1 != X0 )
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f88,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X0
        | ~ v1_relat_1(sK6(X0,X1))
        | sK1 != k1_relat_1(sK6(X0,X1)) )
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f86,f53])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(sK6(X0,X1))
        | ~ v1_relat_1(sK6(X0,X1))
        | sK1 != k1_relat_1(sK6(X0,X1)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK1 )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_3
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK1
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f156,plain,
    ( ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(superposition,[],[f91,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f135,plain,
    ( spl7_8
    | spl7_7 ),
    inference(avatar_split_clause,[],[f131,f118,f133])).

fof(f131,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f129,f41])).

fof(f129,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sK4(k1_tarski(X0),sK0) = X0
      | sK1 != k1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f127,f39])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2(X0,X1))
      | sK4(k1_tarski(X1),sK0) = X1
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X0,X1))
      | sK4(k1_tarski(X1),sK0) = X1
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f124,f40])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2(X1,X0))
      | sK1 != k1_relat_1(sK2(X1,X0))
      | sK4(k1_tarski(X0),sK0) = X0
      | ~ v1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f69,f102])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f82,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f82,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_4
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f83,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f75,f80,f77])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f66,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f34,f63,f59])).

fof(f34,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:55:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1216)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (1204)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (1209)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (1226)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (1204)Refutation not found, incomplete strategy% (1204)------------------------------
% 0.22/0.51  % (1204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1204)Memory used [KB]: 1663
% 0.22/0.51  % (1204)Time elapsed: 0.091 s
% 0.22/0.51  % (1204)------------------------------
% 0.22/0.51  % (1204)------------------------------
% 0.22/0.51  % (1216)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (1206)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1205)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (1207)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (1226)Refutation not found, incomplete strategy% (1226)------------------------------
% 0.22/0.52  % (1226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1226)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1226)Memory used [KB]: 10746
% 0.22/0.52  % (1226)Time elapsed: 0.101 s
% 0.22/0.52  % (1226)------------------------------
% 0.22/0.52  % (1226)------------------------------
% 0.22/0.52  % (1218)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (1217)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f66,f83,f85,f135,f156,f166,f186,f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    spl7_1 | ~spl7_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f209])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    $false | (spl7_1 | ~spl7_9)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | (spl7_1 | ~spl7_9)),
% 0.22/0.53    inference(superposition,[],[f61,f188])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~spl7_9),
% 0.22/0.53    inference(resolution,[],[f185,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl7_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl7_9 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | spl7_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    spl7_9 | spl7_7 | ~spl7_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f182,f133,f118,f184])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl7_7 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    spl7_8 <=> ! [X1] : sK4(k1_tarski(X1),sK0) = X1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) ) | ~spl7_8),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 0.22/0.53    inference(superposition,[],[f180,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) ) | ~spl7_8),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 0.22/0.53    inference(resolution,[],[f178,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) ) | ~spl7_8),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 0.22/0.53    inference(resolution,[],[f174,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) ) | ~spl7_8),
% 0.22/0.53    inference(resolution,[],[f102,f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl7_8),
% 0.22/0.53    inference(superposition,[],[f46,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ( ! [X1] : (sK4(k1_tarski(X1),sK0) = X1) ) | ~spl7_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f133])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_funct_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 0.22/0.53    inference(superposition,[],[f35,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ~spl7_2 | ~spl7_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    $false | (~spl7_2 | ~spl7_3)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f162])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | (~spl7_2 | ~spl7_3)),
% 0.22/0.53    inference(superposition,[],[f91,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl7_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | ~spl7_3),
% 0.22/0.53    inference(equality_resolution,[],[f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) ) | ~spl7_3),
% 0.22/0.53    inference(resolution,[],[f89,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK6(X0,X1)) | k1_xboole_0 != X0 | sK1 != X0) ) | ~spl7_3),
% 0.22/0.53    inference(forward_demodulation,[],[f88,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~v1_relat_1(sK6(X0,X1)) | sK1 != k1_relat_1(sK6(X0,X1))) ) | ~spl7_3),
% 0.22/0.53    inference(forward_demodulation,[],[f86,f53])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | sK1 != k1_relat_1(sK6(X0,X1))) ) | ~spl7_3),
% 0.22/0.53    inference(resolution,[],[f78,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK1) ) | ~spl7_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl7_3 <=> ! [X0] : (k1_relat_1(X0) != sK1 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~spl7_3 | ~spl7_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    $false | (~spl7_3 | ~spl7_7)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | (~spl7_3 | ~spl7_7)),
% 0.22/0.53    inference(superposition,[],[f91,f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl7_7),
% 0.22/0.53    inference(equality_resolution,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl7_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f118])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl7_8 | spl7_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f131,f118,f133])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(superposition,[],[f129,f41])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK4(k1_tarski(X0),sK0) = X0 | sK1 != k1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f127,f39])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | sK4(k1_tarski(X1),sK0) = X1 | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | sK4(k1_tarski(X1),sK0) = X1 | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(resolution,[],[f124,f40])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(sK2(X1,X0)) | sK1 != k1_relat_1(sK2(X1,X0)) | sK4(k1_tarski(X0),sK0) = X0 | ~v1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f69,f102])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 0.22/0.53    inference(resolution,[],[f45,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl7_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    $false | spl7_4),
% 0.22/0.53    inference(resolution,[],[f82,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK0) | spl7_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl7_4 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl7_3 | ~spl7_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f75,f80,f77])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(superposition,[],[f35,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ~spl7_1 | spl7_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f63,f59])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (1216)------------------------------
% 0.22/0.53  % (1216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1216)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (1216)Memory used [KB]: 6268
% 0.22/0.53  % (1216)Time elapsed: 0.099 s
% 0.22/0.53  % (1216)------------------------------
% 0.22/0.53  % (1216)------------------------------
% 0.22/0.53  % (1203)Success in time 0.16 s
%------------------------------------------------------------------------------
