%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:59 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 223 expanded)
%              Number of leaves         :   21 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  434 (1053 expanded)
%              Number of equality atoms :  151 ( 385 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f630,f1013,f1094,f1106,f1343,f1396,f1511,f1690])).

fof(f1690,plain,(
    ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f1689])).

fof(f1689,plain,
    ( $false
    | ~ spl9_26 ),
    inference(trivial_inequality_removal,[],[f1672])).

fof(f1672,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK3 != sK3
    | ~ spl9_26 ),
    inference(superposition,[],[f47,f1009])).

fof(f1009,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | sK3 != X2 )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1008,plain,
    ( spl9_26
  <=> ! [X2] :
        ( k1_xboole_0 = X2
        | sK3 != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK3
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK3
            | k1_relat_1(X1) != sK3
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK3
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK3
              | k1_relat_1(X1) != sK3
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f1511,plain,(
    ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f1406])).

fof(f1406,plain,
    ( $false
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f47,f1395])).

fof(f1395,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1394,plain,
    ( spl9_30
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f1396,plain,
    ( spl9_25
    | spl9_30
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f1381,f1104,f1394,f653])).

fof(f653,plain,
    ( spl9_25
  <=> ! [X1] : sK3 != X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f1104,plain,
    ( spl9_29
  <=> ! [X1,X2] :
        ( sP0(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f1381,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | sK3 != X1 )
    | ~ spl9_29 ),
    inference(resolution,[],[f1380,f1306])).

fof(f1306,plain,
    ( ! [X4,X3] :
        ( sP0(X4,sK6(X3))
        | sK3 != X3 )
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1305,f64])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f1305,plain,
    ( ! [X4,X3] :
        ( sK3 != X3
        | ~ v1_funct_1(sK6(X3))
        | sP0(X4,sK6(X3)) )
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1302,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1302,plain,
    ( ! [X4,X3] :
        ( sK3 != X3
        | ~ v1_relat_1(sK6(X3))
        | ~ v1_funct_1(sK6(X3))
        | sP0(X4,sK6(X3)) )
    | ~ spl9_29 ),
    inference(superposition,[],[f1105,f65])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

fof(f1105,plain,
    ( ! [X2,X1] :
        ( k1_relat_1(X2) != sK3
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | sP0(X1,X2) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f1380,plain,(
    ! [X2,X3] :
      ( ~ sP0(X3,sK6(X2))
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f502,f274])).

fof(f274,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(X4,sK6(X3)),X3)
      | ~ sP0(X4,sK6(X3)) ) ),
    inference(superposition,[],[f59,f65])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK5(X0,X1)) = X0
          & r2_hidden(sK5(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK5(X0,X1)) = X0
        & r2_hidden(sK5(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f502,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X3
      | ~ sP0(X3,sK6(X2))
      | ~ r2_hidden(sK5(X3,sK6(X2)),X2) ) ),
    inference(superposition,[],[f60,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK5(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1343,plain,(
    ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f1342])).

fof(f1342,plain,
    ( $false
    | ~ spl9_25 ),
    inference(equality_resolution,[],[f654])).

fof(f654,plain,
    ( ! [X1] : sK3 != X1
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f653])).

fof(f1106,plain,
    ( spl9_21
    | spl9_29 ),
    inference(avatar_split_clause,[],[f709,f1104,f528])).

fof(f528,plain,
    ( spl9_21
  <=> ! [X5,X7] :
        ( ~ r2_hidden(X7,X5)
        | sK3 != X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f709,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X1,X2)
      | ~ r2_hidden(X3,X0)
      | sK3 != X0
      | k1_relat_1(X2) != sK3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f518,f173])).

fof(f173,plain,(
    ! [X6,X7,X5] :
      ( sK8(X5,X6) = X7
      | sK3 != X5
      | sK3 != k1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f172,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(sK8(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK8(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK8(X0,X1)) = X0
      & v1_funct_1(sK8(X0,X1))
      & v1_relat_1(sK8(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK8(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK8(X0,X1)) = X0
        & v1_funct_1(sK8(X0,X1))
        & v1_relat_1(sK8(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f172,plain,(
    ! [X6,X7,X5] :
      ( sK3 != X5
      | sK8(X5,X6) = X7
      | sK3 != k1_relat_1(X7)
      | ~ v1_relat_1(sK8(X5,X6))
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f167,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_funct_1(sK8(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f167,plain,(
    ! [X6,X7,X5] :
      ( sK3 != X5
      | sK8(X5,X6) = X7
      | sK3 != k1_relat_1(X7)
      | ~ v1_funct_1(sK8(X5,X6))
      | ~ v1_relat_1(sK8(X5,X6))
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f46,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_relat_1(sK8(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK3
      | X1 = X2
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f518,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK8(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP0(X1,sK8(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f515,f77])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK8(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK8(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f80,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK8(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1094,plain,
    ( spl9_25
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f1093,f1011,f653])).

fof(f1011,plain,
    ( spl9_27
  <=> ! [X1] :
        ( ~ sP2(sK6(X1))
        | sK3 != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f1093,plain,
    ( ! [X1] : sK3 != X1
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f1092,f63])).

fof(f1092,plain,
    ( ! [X1] :
        ( sK3 != X1
        | ~ v1_relat_1(sK6(X1)) )
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f1084,f64])).

fof(f1084,plain,
    ( ! [X1] :
        ( sK3 != X1
        | ~ v1_funct_1(sK6(X1))
        | ~ v1_relat_1(sK6(X1)) )
    | ~ spl9_27 ),
    inference(resolution,[],[f1012,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f25,f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1012,plain,
    ( ! [X1] :
        ( ~ sP2(sK6(X1))
        | sK3 != X1 )
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1013,plain,
    ( spl9_26
    | spl9_27
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f1005,f528,f417,f1011,f1008])).

fof(f417,plain,
    ( spl9_13
  <=> ! [X0,X2] :
        ( ~ sP0(X2,X0)
        | k1_relat_1(X0) != sK3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1005,plain,
    ( ! [X2,X1] :
        ( ~ sP2(sK6(X1))
        | k1_xboole_0 = X2
        | sK3 != X1
        | sK3 != X2 )
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f992])).

fof(f992,plain,
    ( ! [X2,X1] :
        ( ~ sP2(sK6(X1))
        | k1_xboole_0 = X2
        | sK3 != X1
        | sK3 != X1
        | sK3 != X2 )
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(resolution,[],[f927,f676])).

fof(f676,plain,
    ( ! [X2,X1] :
        ( sP1(sK6(X1),X2)
        | sK3 != X1
        | sK3 != X2 )
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(resolution,[],[f641,f529])).

fof(f529,plain,
    ( ! [X7,X5] :
        ( ~ r2_hidden(X7,X5)
        | sK3 != X5 )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f528])).

fof(f641,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK4(sK6(X4),X5),X5)
        | sP1(sK6(X4),X5)
        | sK3 != X4 )
    | ~ spl9_13 ),
    inference(resolution,[],[f634,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(sK4(X0,X1),X0)
      | sP1(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sP0(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sP0(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f634,plain,
    ( ! [X4,X3] :
        ( ~ sP0(X4,sK6(X3))
        | sK3 != X3 )
    | ~ spl9_13 ),
    inference(superposition,[],[f418,f65])).

fof(f418,plain,
    ( ! [X2,X0] :
        ( k1_relat_1(X0) != sK3
        | ~ sP0(X2,X0) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f417])).

fof(f927,plain,
    ( ! [X6,X5] :
        ( ~ sP1(sK6(X6),X5)
        | ~ sP2(sK6(X6))
        | k1_xboole_0 = X5
        | sK3 != X6 )
    | ~ spl9_13 ),
    inference(resolution,[],[f207,f675])).

fof(f675,plain,
    ( ! [X0] :
        ( sP1(sK6(X0),k1_xboole_0)
        | sK3 != X0 )
    | ~ spl9_13 ),
    inference(resolution,[],[f641,f88])).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f71,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f207,plain,(
    ! [X2,X3,X1] :
      ( ~ sP1(X1,X3)
      | X2 = X3
      | ~ sP2(X1)
      | ~ sP1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X3,X1] :
      ( X2 = X3
      | ~ sP1(X1,X3)
      | ~ sP2(X1)
      | ~ sP1(X1,X2)
      | ~ sP2(X1) ) ),
    inference(superposition,[],[f54,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP1(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f630,plain,
    ( spl9_13
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f629,f528,f417])).

fof(f629,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) != sK3
        | ~ sP0(X1,X0) )
    | ~ spl9_21 ),
    inference(resolution,[],[f529,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (17528)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.48  % (17528)Refutation not found, incomplete strategy% (17528)------------------------------
% 0.19/0.48  % (17528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (17528)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (17528)Memory used [KB]: 10618
% 0.19/0.48  % (17528)Time elapsed: 0.065 s
% 0.19/0.48  % (17528)------------------------------
% 0.19/0.48  % (17528)------------------------------
% 0.19/0.48  % (17544)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.49  % (17530)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.50  % (17533)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (17525)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (17533)Refutation not found, incomplete strategy% (17533)------------------------------
% 0.19/0.50  % (17533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (17533)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (17533)Memory used [KB]: 10490
% 0.19/0.50  % (17533)Time elapsed: 0.078 s
% 0.19/0.50  % (17533)------------------------------
% 0.19/0.50  % (17533)------------------------------
% 0.19/0.50  % (17523)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (17523)Refutation not found, incomplete strategy% (17523)------------------------------
% 0.19/0.51  % (17523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (17523)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (17523)Memory used [KB]: 10618
% 0.19/0.51  % (17523)Time elapsed: 0.101 s
% 0.19/0.51  % (17523)------------------------------
% 0.19/0.51  % (17523)------------------------------
% 0.19/0.51  % (17529)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.51  % (17524)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.51  % (17539)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.51  % (17526)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.52  % (17541)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.52  % (17537)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.52  % (17534)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.52  % (17536)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.53  % (17543)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.53  % (17547)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.53  % (17540)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.53  % (17527)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.54  % (17527)Refutation not found, incomplete strategy% (17527)------------------------------
% 0.19/0.54  % (17527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (17527)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (17527)Memory used [KB]: 6140
% 0.19/0.54  % (17527)Time elapsed: 0.114 s
% 0.19/0.54  % (17527)------------------------------
% 0.19/0.54  % (17527)------------------------------
% 0.19/0.54  % (17522)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.54  % (17531)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.47/0.54  % (17532)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.47/0.54  % (17542)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.47/0.55  % (17535)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.47/0.55  % (17545)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.47/0.55  % (17535)Refutation not found, incomplete strategy% (17535)------------------------------
% 1.47/0.55  % (17535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (17535)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (17535)Memory used [KB]: 6012
% 1.47/0.55  % (17535)Time elapsed: 0.150 s
% 1.47/0.55  % (17535)------------------------------
% 1.47/0.55  % (17535)------------------------------
% 1.47/0.55  % (17546)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.62/0.56  % (17522)Refutation not found, incomplete strategy% (17522)------------------------------
% 1.62/0.56  % (17522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.56  % (17522)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.56  
% 1.62/0.56  % (17522)Memory used [KB]: 10490
% 1.62/0.56  % (17522)Time elapsed: 0.152 s
% 1.62/0.56  % (17522)------------------------------
% 1.62/0.56  % (17522)------------------------------
% 1.62/0.56  % (17538)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.62/0.59  % (17526)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f1699,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f630,f1013,f1094,f1106,f1343,f1396,f1511,f1690])).
% 1.62/0.59  fof(f1690,plain,(
% 1.62/0.59    ~spl9_26),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f1689])).
% 1.62/0.59  fof(f1689,plain,(
% 1.62/0.59    $false | ~spl9_26),
% 1.62/0.59    inference(trivial_inequality_removal,[],[f1672])).
% 1.62/0.59  fof(f1672,plain,(
% 1.62/0.59    k1_xboole_0 != k1_xboole_0 | sK3 != sK3 | ~spl9_26),
% 1.62/0.59    inference(superposition,[],[f47,f1009])).
% 1.62/0.59  fof(f1009,plain,(
% 1.62/0.59    ( ! [X2] : (k1_xboole_0 = X2 | sK3 != X2) ) | ~spl9_26),
% 1.62/0.59    inference(avatar_component_clause,[],[f1008])).
% 1.62/0.59  fof(f1008,plain,(
% 1.62/0.59    spl9_26 <=> ! [X2] : (k1_xboole_0 = X2 | sK3 != X2)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    k1_xboole_0 != sK3),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f14,plain,(
% 1.62/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.62/0.59    inference(flattening,[],[f13])).
% 1.62/0.59  fof(f13,plain,(
% 1.62/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.62/0.59    inference(ennf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,negated_conjecture,(
% 1.62/0.59    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.62/0.59    inference(negated_conjecture,[],[f11])).
% 1.62/0.59  fof(f11,conjecture,(
% 1.62/0.59    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 1.62/0.59  fof(f1511,plain,(
% 1.62/0.59    ~spl9_30),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f1406])).
% 1.62/0.59  fof(f1406,plain,(
% 1.62/0.59    $false | ~spl9_30),
% 1.62/0.59    inference(subsumption_resolution,[],[f47,f1395])).
% 1.62/0.59  fof(f1395,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl9_30),
% 1.62/0.59    inference(avatar_component_clause,[],[f1394])).
% 1.62/0.59  fof(f1394,plain,(
% 1.62/0.59    spl9_30 <=> ! [X0] : k1_xboole_0 = X0),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.62/0.59  fof(f1396,plain,(
% 1.62/0.59    spl9_25 | spl9_30 | ~spl9_29),
% 1.62/0.59    inference(avatar_split_clause,[],[f1381,f1104,f1394,f653])).
% 1.62/0.59  fof(f653,plain,(
% 1.62/0.59    spl9_25 <=> ! [X1] : sK3 != X1),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.62/0.59  fof(f1104,plain,(
% 1.62/0.59    spl9_29 <=> ! [X1,X2] : (sP0(X1,X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK3)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.62/0.59  fof(f1381,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_xboole_0 = X0 | sK3 != X1) ) | ~spl9_29),
% 1.62/0.59    inference(resolution,[],[f1380,f1306])).
% 1.62/0.59  fof(f1306,plain,(
% 1.62/0.59    ( ! [X4,X3] : (sP0(X4,sK6(X3)) | sK3 != X3) ) | ~spl9_29),
% 1.62/0.59    inference(subsumption_resolution,[],[f1305,f64])).
% 1.62/0.59  fof(f64,plain,(
% 1.62/0.59    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.62/0.59  fof(f1305,plain,(
% 1.62/0.59    ( ! [X4,X3] : (sK3 != X3 | ~v1_funct_1(sK6(X3)) | sP0(X4,sK6(X3))) ) | ~spl9_29),
% 1.62/0.59    inference(subsumption_resolution,[],[f1302,f63])).
% 1.62/0.59  fof(f63,plain,(
% 1.62/0.59    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f39])).
% 1.62/0.59  fof(f1302,plain,(
% 1.62/0.59    ( ! [X4,X3] : (sK3 != X3 | ~v1_relat_1(sK6(X3)) | ~v1_funct_1(sK6(X3)) | sP0(X4,sK6(X3))) ) | ~spl9_29),
% 1.62/0.59    inference(superposition,[],[f1105,f65])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f39])).
% 1.62/0.59  fof(f1105,plain,(
% 1.62/0.59    ( ! [X2,X1] : (k1_relat_1(X2) != sK3 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | sP0(X1,X2)) ) | ~spl9_29),
% 1.62/0.59    inference(avatar_component_clause,[],[f1104])).
% 1.62/0.59  fof(f1380,plain,(
% 1.62/0.59    ( ! [X2,X3] : (~sP0(X3,sK6(X2)) | k1_xboole_0 = X3) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f502,f274])).
% 1.62/0.59  fof(f274,plain,(
% 1.62/0.59    ( ! [X4,X3] : (r2_hidden(sK5(X4,sK6(X3)),X3) | ~sP0(X4,sK6(X3))) )),
% 1.62/0.59    inference(superposition,[],[f59,f65])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f37])).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK5(X0,X1)) = X0 & r2_hidden(sK5(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK5(X0,X1)) = X0 & r2_hidden(sK5(X0,X1),k1_relat_1(X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.62/0.59    inference(rectify,[],[f34])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 1.62/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.62/0.60  fof(f502,plain,(
% 1.62/0.60    ( ! [X2,X3] : (k1_xboole_0 = X3 | ~sP0(X3,sK6(X2)) | ~r2_hidden(sK5(X3,sK6(X2)),X2)) )),
% 1.62/0.60    inference(superposition,[],[f60,f66])).
% 1.62/0.60  fof(f66,plain,(
% 1.62/0.60    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f39])).
% 1.62/0.60  fof(f60,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_funct_1(X1,sK5(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f37])).
% 1.62/0.60  fof(f1343,plain,(
% 1.62/0.60    ~spl9_25),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f1342])).
% 1.62/0.60  fof(f1342,plain,(
% 1.62/0.60    $false | ~spl9_25),
% 1.62/0.60    inference(equality_resolution,[],[f654])).
% 1.62/0.60  fof(f654,plain,(
% 1.62/0.60    ( ! [X1] : (sK3 != X1) ) | ~spl9_25),
% 1.62/0.60    inference(avatar_component_clause,[],[f653])).
% 1.62/0.60  fof(f1106,plain,(
% 1.62/0.60    spl9_21 | spl9_29),
% 1.62/0.60    inference(avatar_split_clause,[],[f709,f1104,f528])).
% 1.62/0.60  fof(f528,plain,(
% 1.62/0.60    spl9_21 <=> ! [X5,X7] : (~r2_hidden(X7,X5) | sK3 != X5)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.62/0.60  fof(f709,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (sP0(X1,X2) | ~r2_hidden(X3,X0) | sK3 != X0 | k1_relat_1(X2) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.62/0.60    inference(superposition,[],[f518,f173])).
% 1.62/0.60  fof(f173,plain,(
% 1.62/0.60    ( ! [X6,X7,X5] : (sK8(X5,X6) = X7 | sK3 != X5 | sK3 != k1_relat_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f172,f75])).
% 1.62/0.60  fof(f75,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_relat_1(sK8(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f45,plain,(
% 1.62/0.60    ! [X0,X1] : (! [X3] : (k1_funct_1(sK8(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK8(X0,X1)) = X0 & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1)))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f44])).
% 1.62/0.60  fof(f44,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK8(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK8(X0,X1)) = X0 & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f22,plain,(
% 1.62/0.60    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.62/0.60    inference(ennf_transformation,[],[f8])).
% 1.62/0.60  fof(f8,axiom,(
% 1.62/0.60    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.62/0.60  fof(f172,plain,(
% 1.62/0.60    ( ! [X6,X7,X5] : (sK3 != X5 | sK8(X5,X6) = X7 | sK3 != k1_relat_1(X7) | ~v1_relat_1(sK8(X5,X6)) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f167,f76])).
% 1.62/0.60  fof(f76,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_funct_1(sK8(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f167,plain,(
% 1.62/0.60    ( ! [X6,X7,X5] : (sK3 != X5 | sK8(X5,X6) = X7 | sK3 != k1_relat_1(X7) | ~v1_funct_1(sK8(X5,X6)) | ~v1_relat_1(sK8(X5,X6)) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 1.62/0.60    inference(superposition,[],[f46,f77])).
% 1.62/0.60  fof(f77,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_relat_1(sK8(X0,X1)) = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f46,plain,(
% 1.62/0.60    ( ! [X2,X1] : (k1_relat_1(X2) != sK3 | X1 = X2 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f28])).
% 1.62/0.60  fof(f518,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (sP0(X1,sK8(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f517])).
% 1.62/0.60  fof(f517,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP0(X1,sK8(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(forward_demodulation,[],[f515,f77])).
% 1.62/0.60  fof(f515,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (sP0(X1,sK8(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK8(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(superposition,[],[f80,f78])).
% 1.62/0.60  fof(f78,plain,(
% 1.62/0.60    ( ! [X0,X3,X1] : (k1_funct_1(sK8(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f80,plain,(
% 1.62/0.60    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 1.62/0.60    inference(equality_resolution,[],[f61])).
% 1.62/0.60  fof(f61,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f37])).
% 1.62/0.60  fof(f1094,plain,(
% 1.62/0.60    spl9_25 | ~spl9_27),
% 1.62/0.60    inference(avatar_split_clause,[],[f1093,f1011,f653])).
% 1.62/0.60  fof(f1011,plain,(
% 1.62/0.60    spl9_27 <=> ! [X1] : (~sP2(sK6(X1)) | sK3 != X1)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.62/0.60  fof(f1093,plain,(
% 1.62/0.60    ( ! [X1] : (sK3 != X1) ) | ~spl9_27),
% 1.62/0.60    inference(subsumption_resolution,[],[f1092,f63])).
% 1.62/0.60  fof(f1092,plain,(
% 1.62/0.60    ( ! [X1] : (sK3 != X1 | ~v1_relat_1(sK6(X1))) ) | ~spl9_27),
% 1.62/0.60    inference(subsumption_resolution,[],[f1084,f64])).
% 1.62/0.60  fof(f1084,plain,(
% 1.62/0.60    ( ! [X1] : (sK3 != X1 | ~v1_funct_1(sK6(X1)) | ~v1_relat_1(sK6(X1))) ) | ~spl9_27),
% 1.62/0.60    inference(resolution,[],[f1012,f62])).
% 1.62/0.60  fof(f62,plain,(
% 1.62/0.60    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(definition_folding,[],[f19,f25,f24,f23])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 1.62/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.62/0.60  fof(f25,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 1.62/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.62/0.60  fof(f19,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(flattening,[],[f18])).
% 1.62/0.60  fof(f18,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f7])).
% 1.62/0.60  fof(f7,axiom,(
% 1.62/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.62/0.60  fof(f1012,plain,(
% 1.62/0.60    ( ! [X1] : (~sP2(sK6(X1)) | sK3 != X1) ) | ~spl9_27),
% 1.62/0.60    inference(avatar_component_clause,[],[f1011])).
% 1.62/0.60  fof(f1013,plain,(
% 1.62/0.60    spl9_26 | spl9_27 | ~spl9_13 | ~spl9_21),
% 1.62/0.60    inference(avatar_split_clause,[],[f1005,f528,f417,f1011,f1008])).
% 1.62/0.60  fof(f417,plain,(
% 1.62/0.60    spl9_13 <=> ! [X0,X2] : (~sP0(X2,X0) | k1_relat_1(X0) != sK3)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.62/0.60  fof(f1005,plain,(
% 1.62/0.60    ( ! [X2,X1] : (~sP2(sK6(X1)) | k1_xboole_0 = X2 | sK3 != X1 | sK3 != X2) ) | (~spl9_13 | ~spl9_21)),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f992])).
% 1.62/0.60  fof(f992,plain,(
% 1.62/0.60    ( ! [X2,X1] : (~sP2(sK6(X1)) | k1_xboole_0 = X2 | sK3 != X1 | sK3 != X1 | sK3 != X2) ) | (~spl9_13 | ~spl9_21)),
% 1.62/0.60    inference(resolution,[],[f927,f676])).
% 1.62/0.60  fof(f676,plain,(
% 1.62/0.60    ( ! [X2,X1] : (sP1(sK6(X1),X2) | sK3 != X1 | sK3 != X2) ) | (~spl9_13 | ~spl9_21)),
% 1.62/0.60    inference(resolution,[],[f641,f529])).
% 1.62/0.60  fof(f529,plain,(
% 1.62/0.60    ( ! [X7,X5] : (~r2_hidden(X7,X5) | sK3 != X5) ) | ~spl9_21),
% 1.62/0.60    inference(avatar_component_clause,[],[f528])).
% 1.62/0.60  fof(f641,plain,(
% 1.62/0.60    ( ! [X4,X5] : (r2_hidden(sK4(sK6(X4),X5),X5) | sP1(sK6(X4),X5) | sK3 != X4) ) | ~spl9_13),
% 1.62/0.60    inference(resolution,[],[f634,f57])).
% 1.62/0.60  fof(f57,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sP0(sK4(X0,X1),X0) | sP1(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f33])).
% 1.62/0.60  fof(f33,plain,(
% 1.62/0.60    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (sP0(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.62/0.60  fof(f32,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (sP0(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f31,plain,(
% 1.62/0.60    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.62/0.60    inference(rectify,[],[f30])).
% 1.62/0.60  fof(f30,plain,(
% 1.62/0.60    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.62/0.60    inference(nnf_transformation,[],[f24])).
% 1.62/0.60  fof(f634,plain,(
% 1.62/0.60    ( ! [X4,X3] : (~sP0(X4,sK6(X3)) | sK3 != X3) ) | ~spl9_13),
% 1.62/0.60    inference(superposition,[],[f418,f65])).
% 1.62/0.60  fof(f418,plain,(
% 1.62/0.60    ( ! [X2,X0] : (k1_relat_1(X0) != sK3 | ~sP0(X2,X0)) ) | ~spl9_13),
% 1.62/0.60    inference(avatar_component_clause,[],[f417])).
% 1.62/0.60  fof(f927,plain,(
% 1.62/0.60    ( ! [X6,X5] : (~sP1(sK6(X6),X5) | ~sP2(sK6(X6)) | k1_xboole_0 = X5 | sK3 != X6) ) | ~spl9_13),
% 1.62/0.60    inference(resolution,[],[f207,f675])).
% 1.62/0.60  fof(f675,plain,(
% 1.62/0.60    ( ! [X0] : (sP1(sK6(X0),k1_xboole_0) | sK3 != X0) ) | ~spl9_13),
% 1.62/0.60    inference(resolution,[],[f641,f88])).
% 1.62/0.60  fof(f88,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(superposition,[],[f71,f81])).
% 1.62/0.60  fof(f81,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(equality_resolution,[],[f74])).
% 1.62/0.60  fof(f74,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.62/0.60    inference(cnf_transformation,[],[f43])).
% 1.62/0.60  fof(f43,plain,(
% 1.62/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.62/0.60    inference(flattening,[],[f42])).
% 1.62/0.60  fof(f42,plain,(
% 1.62/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.62/0.60    inference(nnf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.62/0.60  fof(f71,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f4])).
% 1.62/0.60  fof(f4,axiom,(
% 1.62/0.60    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.62/0.60  fof(f207,plain,(
% 1.62/0.60    ( ! [X2,X3,X1] : (~sP1(X1,X3) | X2 = X3 | ~sP2(X1) | ~sP1(X1,X2)) )),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f203])).
% 1.62/0.60  fof(f203,plain,(
% 1.62/0.60    ( ! [X2,X3,X1] : (X2 = X3 | ~sP1(X1,X3) | ~sP2(X1) | ~sP1(X1,X2) | ~sP2(X1)) )),
% 1.62/0.60    inference(superposition,[],[f54,f54])).
% 1.62/0.60  fof(f54,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP1(X0,X1) | ~sP2(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 1.62/0.60    inference(nnf_transformation,[],[f25])).
% 1.62/0.60  fof(f630,plain,(
% 1.62/0.60    spl9_13 | ~spl9_21),
% 1.62/0.60    inference(avatar_split_clause,[],[f629,f528,f417])).
% 1.62/0.60  fof(f629,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_relat_1(X0) != sK3 | ~sP0(X1,X0)) ) | ~spl9_21),
% 1.62/0.60    inference(resolution,[],[f529,f59])).
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (17526)------------------------------
% 1.62/0.60  % (17526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (17526)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (17526)Memory used [KB]: 6780
% 1.62/0.60  % (17526)Time elapsed: 0.193 s
% 1.62/0.60  % (17526)------------------------------
% 1.62/0.60  % (17526)------------------------------
% 1.62/0.60  % (17521)Success in time 0.235 s
%------------------------------------------------------------------------------
