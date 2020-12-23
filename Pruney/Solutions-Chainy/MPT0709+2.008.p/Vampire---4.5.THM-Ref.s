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
% DateTime   : Thu Dec  3 12:54:36 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 250 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  425 ( 904 expanded)
%              Number of equality atoms :   56 ( 150 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1606,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f202,f204,f206,f208,f219,f226,f274,f607,f739,f896,f1254,f1605])).

fof(f1605,plain,
    ( spl5_2
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f1604])).

fof(f1604,plain,
    ( $false
    | spl5_2
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(resolution,[],[f1587,f635])).

fof(f635,plain,
    ( ! [X13] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X13)),X13)
    | ~ spl5_13 ),
    inference(superposition,[],[f352,f606])).

fof(f606,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl5_13
  <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f352,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f349,f106])).

fof(f106,plain,(
    ! [X0,X1] : sP0(X1,X0,k6_subset_1(X0,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f94,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f349,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(X2,X1)
      | r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f146,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ sP0(X3,X1,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f88,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f1587,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f1253,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_2
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1253,plain,
    ( ! [X10,X9] :
        ( r1_tarski(k10_relat_1(sK2,X9),X10)
        | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10)) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f1252,plain,
    ( spl5_20
  <=> ! [X9,X10] :
        ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10))
        | r1_tarski(k10_relat_1(sK2,X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1254,plain,
    ( ~ spl5_5
    | spl5_20
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1244,f894,f1252,f191])).

fof(f191,plain,
    ( spl5_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f894,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1244,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10))
        | r1_tarski(k10_relat_1(sK2,X9),X10)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_16 ),
    inference(resolution,[],[f895,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f895,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | r1_tarski(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f894])).

fof(f896,plain,
    ( ~ spl5_5
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f892,f894,f731,f191])).

fof(f731,plain,
    ( spl5_14
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f892,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f87,f62])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_tarski(sK1,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f45])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_tarski(sK1,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f739,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f733,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f733,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f731])).

fof(f607,plain,
    ( ~ spl5_5
    | spl5_13
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f603,f272,f216,f605,f191])).

fof(f216,plain,
    ( spl5_9
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f272,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f603,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2)))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f602,f277])).

fof(f277,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f275,f218])).

fof(f218,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f216])).

fof(f275,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl5_11 ),
    inference(resolution,[],[f273,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f272])).

fof(f602,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK2,k1_relat_1(sK2))))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f107,f60])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f101,f100])).

fof(f100,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f73,f96,f70,f70])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f96])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f274,plain,
    ( ~ spl5_5
    | spl5_11 ),
    inference(avatar_split_clause,[],[f270,f272,f191])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f226,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f220,f59])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_8 ),
    inference(resolution,[],[f214,f74])).

fof(f214,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_8
  <=> r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f219,plain,
    ( ~ spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f210,f199,f216,f212])).

fof(f199,plain,
    ( spl5_7
  <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f210,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl5_7 ),
    inference(resolution,[],[f201,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f201,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f208,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f197,f104])).

fof(f197,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_6
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f206,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f188,f61])).

fof(f61,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f188,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl5_1 ),
    inference(resolution,[],[f186,f123])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_1
  <=> r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f186,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f204,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f193,f59])).

fof(f193,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f191])).

fof(f202,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f189,f199,f195,f191])).

fof(f189,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f186,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f129,plain,
    ( ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f115,f121,f125])).

fof(f115,plain,
    ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1) ),
    inference(extensionality_resolution,[],[f81,f63])).

fof(f63,plain,(
    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (3444)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.50  % (3436)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (3429)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (3427)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (3436)Refutation not found, incomplete strategy% (3436)------------------------------
% 0.22/0.51  % (3436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3442)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (3431)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (3436)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3436)Memory used [KB]: 10618
% 0.22/0.51  % (3436)Time elapsed: 0.087 s
% 0.22/0.51  % (3436)------------------------------
% 0.22/0.51  % (3436)------------------------------
% 0.22/0.52  % (3429)Refutation not found, incomplete strategy% (3429)------------------------------
% 0.22/0.52  % (3429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3429)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3429)Memory used [KB]: 10746
% 0.22/0.52  % (3429)Time elapsed: 0.093 s
% 0.22/0.52  % (3429)------------------------------
% 0.22/0.52  % (3429)------------------------------
% 0.22/0.52  % (3432)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (3430)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (3433)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (3434)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (3419)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (3448)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (3424)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (3425)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (3422)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (3437)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (3446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (3421)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (3441)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (3441)Refutation not found, incomplete strategy% (3441)------------------------------
% 0.22/0.53  % (3441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3441)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3441)Memory used [KB]: 10746
% 0.22/0.53  % (3441)Time elapsed: 0.089 s
% 0.22/0.53  % (3441)------------------------------
% 0.22/0.53  % (3441)------------------------------
% 0.22/0.53  % (3435)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (3420)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (3438)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (3447)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (3423)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (3440)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (3445)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (3443)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (3426)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (3428)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (3439)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.94/0.62  % (3431)Refutation found. Thanks to Tanya!
% 1.94/0.62  % SZS status Theorem for theBenchmark
% 1.94/0.62  % SZS output start Proof for theBenchmark
% 1.94/0.62  fof(f1606,plain,(
% 1.94/0.62    $false),
% 1.94/0.62    inference(avatar_sat_refutation,[],[f129,f202,f204,f206,f208,f219,f226,f274,f607,f739,f896,f1254,f1605])).
% 1.94/0.62  fof(f1605,plain,(
% 1.94/0.62    spl5_2 | ~spl5_13 | ~spl5_20),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f1604])).
% 1.94/0.62  fof(f1604,plain,(
% 1.94/0.62    $false | (spl5_2 | ~spl5_13 | ~spl5_20)),
% 1.94/0.62    inference(resolution,[],[f1587,f635])).
% 1.94/0.62  fof(f635,plain,(
% 1.94/0.62    ( ! [X13] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X13)),X13)) ) | ~spl5_13),
% 1.94/0.62    inference(superposition,[],[f352,f606])).
% 1.94/0.62  fof(f606,plain,(
% 1.94/0.62    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2)))) ) | ~spl5_13),
% 1.94/0.62    inference(avatar_component_clause,[],[f605])).
% 1.94/0.62  fof(f605,plain,(
% 1.94/0.62    spl5_13 <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2)))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.94/0.62  fof(f352,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.94/0.62    inference(resolution,[],[f349,f106])).
% 1.94/0.62  fof(f106,plain,(
% 1.94/0.62    ( ! [X0,X1] : (sP0(X1,X0,k6_subset_1(X0,X1))) )),
% 1.94/0.62    inference(equality_resolution,[],[f103])).
% 1.94/0.62  fof(f103,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.94/0.62    inference(definition_unfolding,[],[f94,f70])).
% 1.94/0.62  fof(f70,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f11])).
% 1.94/0.62  fof(f11,axiom,(
% 1.94/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.94/0.62  fof(f94,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.62    inference(cnf_transformation,[],[f58])).
% 1.94/0.62  fof(f58,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.94/0.62    inference(nnf_transformation,[],[f44])).
% 1.94/0.62  fof(f44,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.94/0.62    inference(definition_folding,[],[f3,f43])).
% 1.94/0.62  fof(f43,plain,(
% 1.94/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.94/0.62  fof(f3,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.94/0.62  fof(f349,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(X2,X1)) )),
% 1.94/0.62    inference(duplicate_literal_removal,[],[f344])).
% 1.94/0.62  fof(f344,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(X2,X1) | r1_tarski(X2,X1)) )),
% 1.94/0.62    inference(resolution,[],[f146,f83])).
% 1.94/0.62  fof(f83,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f52])).
% 1.94/0.62  fof(f52,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 1.94/0.62  fof(f51,plain,(
% 1.94/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f50,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(rectify,[],[f49])).
% 1.94/0.62  fof(f49,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(nnf_transformation,[],[f36])).
% 1.94/0.62  fof(f36,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.62    inference(ennf_transformation,[],[f2])).
% 1.94/0.62  fof(f2,axiom,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.94/0.62  fof(f146,plain,(
% 1.94/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~sP0(X3,X1,X2) | r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(resolution,[],[f88,f84])).
% 1.94/0.62  fof(f84,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f52])).
% 1.94/0.62  fof(f88,plain,(
% 1.94/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f57])).
% 1.94/0.62  fof(f57,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 1.94/0.62  fof(f56,plain,(
% 1.94/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f55,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.94/0.62    inference(rectify,[],[f54])).
% 1.94/0.62  fof(f54,plain,(
% 1.94/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.94/0.62    inference(flattening,[],[f53])).
% 1.94/0.62  fof(f53,plain,(
% 1.94/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.94/0.62    inference(nnf_transformation,[],[f43])).
% 1.94/0.62  fof(f1587,plain,(
% 1.94/0.62    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | (spl5_2 | ~spl5_20)),
% 1.94/0.62    inference(resolution,[],[f1253,f127])).
% 1.94/0.62  fof(f127,plain,(
% 1.94/0.62    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1) | spl5_2),
% 1.94/0.62    inference(avatar_component_clause,[],[f125])).
% 1.94/0.62  fof(f125,plain,(
% 1.94/0.62    spl5_2 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.94/0.62  fof(f1253,plain,(
% 1.94/0.62    ( ! [X10,X9] : (r1_tarski(k10_relat_1(sK2,X9),X10) | ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10))) ) | ~spl5_20),
% 1.94/0.62    inference(avatar_component_clause,[],[f1252])).
% 1.94/0.62  fof(f1252,plain,(
% 1.94/0.62    spl5_20 <=> ! [X9,X10] : (~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10)) | r1_tarski(k10_relat_1(sK2,X9),X10))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.94/0.62  fof(f1254,plain,(
% 1.94/0.62    ~spl5_5 | spl5_20 | ~spl5_16),
% 1.94/0.62    inference(avatar_split_clause,[],[f1244,f894,f1252,f191])).
% 1.94/0.62  fof(f191,plain,(
% 1.94/0.62    spl5_5 <=> v1_relat_1(sK2)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.94/0.62  fof(f894,plain,(
% 1.94/0.62    spl5_16 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,k1_relat_1(sK2)))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.94/0.62  fof(f1244,plain,(
% 1.94/0.62    ( ! [X10,X9] : (~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X9)),k9_relat_1(sK2,X10)) | r1_tarski(k10_relat_1(sK2,X9),X10) | ~v1_relat_1(sK2)) ) | ~spl5_16),
% 1.94/0.62    inference(resolution,[],[f895,f74])).
% 1.94/0.62  fof(f74,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f28])).
% 1.94/0.62  fof(f28,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f14])).
% 1.94/0.62  fof(f14,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.94/0.62  fof(f895,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | r1_tarski(X0,X1)) ) | ~spl5_16),
% 1.94/0.62    inference(avatar_component_clause,[],[f894])).
% 1.94/0.62  fof(f896,plain,(
% 1.94/0.62    ~spl5_5 | ~spl5_14 | spl5_16),
% 1.94/0.62    inference(avatar_split_clause,[],[f892,f894,f731,f191])).
% 1.94/0.62  fof(f731,plain,(
% 1.94/0.62    spl5_14 <=> v1_funct_1(sK2)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.94/0.62  fof(f892,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.94/0.62    inference(resolution,[],[f87,f62])).
% 1.94/0.62  fof(f62,plain,(
% 1.94/0.62    v2_funct_1(sK2)),
% 1.94/0.62    inference(cnf_transformation,[],[f46])).
% 1.94/0.62  fof(f46,plain,(
% 1.94/0.62    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f45])).
% 1.94/0.62  fof(f45,plain,(
% 1.94/0.62    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f25,plain,(
% 1.94/0.62    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f24])).
% 1.94/0.62  fof(f24,plain,(
% 1.94/0.62    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.94/0.62    inference(ennf_transformation,[],[f23])).
% 1.94/0.62  fof(f23,negated_conjecture,(
% 1.94/0.62    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.94/0.62    inference(negated_conjecture,[],[f22])).
% 1.94/0.62  fof(f22,conjecture,(
% 1.94/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.94/0.62  fof(f87,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f42])).
% 1.94/0.62  fof(f42,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.94/0.62    inference(flattening,[],[f41])).
% 1.94/0.62  fof(f41,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.94/0.62    inference(ennf_transformation,[],[f21])).
% 1.94/0.62  fof(f21,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.94/0.62  fof(f739,plain,(
% 1.94/0.62    spl5_14),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f738])).
% 1.94/0.62  fof(f738,plain,(
% 1.94/0.62    $false | spl5_14),
% 1.94/0.62    inference(resolution,[],[f733,f60])).
% 1.94/0.62  fof(f60,plain,(
% 1.94/0.62    v1_funct_1(sK2)),
% 1.94/0.62    inference(cnf_transformation,[],[f46])).
% 1.94/0.62  fof(f733,plain,(
% 1.94/0.62    ~v1_funct_1(sK2) | spl5_14),
% 1.94/0.62    inference(avatar_component_clause,[],[f731])).
% 1.94/0.62  fof(f607,plain,(
% 1.94/0.62    ~spl5_5 | spl5_13 | ~spl5_9 | ~spl5_11),
% 1.94/0.62    inference(avatar_split_clause,[],[f603,f272,f216,f605,f191])).
% 1.94/0.62  fof(f216,plain,(
% 1.94/0.62    spl5_9 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.94/0.62  fof(f272,plain,(
% 1.94/0.62    spl5_11 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.94/0.62  fof(f603,plain,(
% 1.94/0.62    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k2_relat_1(sK2))) | ~v1_relat_1(sK2)) ) | (~spl5_9 | ~spl5_11)),
% 1.94/0.62    inference(forward_demodulation,[],[f602,f277])).
% 1.94/0.62  fof(f277,plain,(
% 1.94/0.62    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) | (~spl5_9 | ~spl5_11)),
% 1.94/0.62    inference(forward_demodulation,[],[f275,f218])).
% 1.94/0.62  fof(f218,plain,(
% 1.94/0.62    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl5_9),
% 1.94/0.62    inference(avatar_component_clause,[],[f216])).
% 1.94/0.62  fof(f275,plain,(
% 1.94/0.62    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) | ~spl5_11),
% 1.94/0.62    inference(resolution,[],[f273,f104])).
% 1.94/0.62  fof(f104,plain,(
% 1.94/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.94/0.62    inference(equality_resolution,[],[f80])).
% 1.94/0.62  fof(f80,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.94/0.62    inference(cnf_transformation,[],[f48])).
% 1.94/0.62  fof(f48,plain,(
% 1.94/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.94/0.62    inference(flattening,[],[f47])).
% 1.94/0.62  fof(f47,plain,(
% 1.94/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.94/0.62    inference(nnf_transformation,[],[f4])).
% 1.94/0.62  fof(f4,axiom,(
% 1.94/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.94/0.62  fof(f273,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl5_11),
% 1.94/0.62    inference(avatar_component_clause,[],[f272])).
% 1.94/0.62  fof(f602,plain,(
% 1.94/0.62    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)) )),
% 1.94/0.62    inference(resolution,[],[f107,f60])).
% 1.94/0.62  fof(f107,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(forward_demodulation,[],[f101,f100])).
% 1.94/0.62  fof(f100,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.94/0.62    inference(definition_unfolding,[],[f73,f96,f70,f70])).
% 1.94/0.62  fof(f96,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.94/0.62    inference(definition_unfolding,[],[f71,f72])).
% 1.94/0.62  fof(f72,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f10])).
% 1.94/0.62  fof(f10,axiom,(
% 1.94/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.94/0.62  fof(f71,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f12])).
% 1.94/0.62  fof(f12,axiom,(
% 1.94/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.94/0.62  fof(f73,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f8])).
% 1.94/0.62  fof(f8,axiom,(
% 1.94/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.94/0.62  fof(f101,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f77,f96])).
% 1.94/0.62  fof(f77,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f33])).
% 1.94/0.62  fof(f33,plain,(
% 1.94/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f32])).
% 1.94/0.62  fof(f32,plain,(
% 1.94/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.94/0.62    inference(ennf_transformation,[],[f20])).
% 1.94/0.62  fof(f20,axiom,(
% 1.94/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.94/0.62  fof(f274,plain,(
% 1.94/0.62    ~spl5_5 | spl5_11),
% 1.94/0.62    inference(avatar_split_clause,[],[f270,f272,f191])).
% 1.94/0.62  fof(f270,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 1.94/0.62    inference(resolution,[],[f78,f60])).
% 1.94/0.62  fof(f78,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f35])).
% 1.94/0.62  fof(f35,plain,(
% 1.94/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f34])).
% 1.94/0.62  fof(f34,plain,(
% 1.94/0.62    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.94/0.62    inference(ennf_transformation,[],[f19])).
% 1.94/0.62  fof(f19,axiom,(
% 1.94/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.94/0.62  fof(f226,plain,(
% 1.94/0.62    spl5_8),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f225])).
% 1.94/0.62  fof(f225,plain,(
% 1.94/0.62    $false | spl5_8),
% 1.94/0.62    inference(resolution,[],[f220,f59])).
% 1.94/0.62  fof(f59,plain,(
% 1.94/0.62    v1_relat_1(sK2)),
% 1.94/0.62    inference(cnf_transformation,[],[f46])).
% 1.94/0.62  fof(f220,plain,(
% 1.94/0.62    ~v1_relat_1(sK2) | spl5_8),
% 1.94/0.62    inference(resolution,[],[f214,f74])).
% 1.94/0.62  fof(f214,plain,(
% 1.94/0.62    ~r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) | spl5_8),
% 1.94/0.62    inference(avatar_component_clause,[],[f212])).
% 1.94/0.62  fof(f212,plain,(
% 1.94/0.62    spl5_8 <=> r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.94/0.62  fof(f219,plain,(
% 1.94/0.62    ~spl5_8 | spl5_9 | ~spl5_7),
% 1.94/0.62    inference(avatar_split_clause,[],[f210,f199,f216,f212])).
% 1.94/0.62  fof(f199,plain,(
% 1.94/0.62    spl5_7 <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.94/0.62  fof(f210,plain,(
% 1.94/0.62    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k1_relat_1(sK2)) | ~spl5_7),
% 1.94/0.62    inference(resolution,[],[f201,f81])).
% 1.94/0.62  fof(f81,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f48])).
% 1.94/0.62  fof(f201,plain,(
% 1.94/0.62    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~spl5_7),
% 1.94/0.62    inference(avatar_component_clause,[],[f199])).
% 1.94/0.62  fof(f208,plain,(
% 1.94/0.62    spl5_6),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f207])).
% 1.94/0.62  fof(f207,plain,(
% 1.94/0.62    $false | spl5_6),
% 1.94/0.62    inference(resolution,[],[f197,f104])).
% 1.94/0.62  fof(f197,plain,(
% 1.94/0.62    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | spl5_6),
% 1.94/0.62    inference(avatar_component_clause,[],[f195])).
% 1.94/0.62  fof(f195,plain,(
% 1.94/0.62    spl5_6 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.94/0.62  fof(f206,plain,(
% 1.94/0.62    spl5_1),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f205])).
% 1.94/0.62  fof(f205,plain,(
% 1.94/0.62    $false | spl5_1),
% 1.94/0.62    inference(resolution,[],[f188,f61])).
% 1.94/0.62  fof(f61,plain,(
% 1.94/0.62    r1_tarski(sK1,k1_relat_1(sK2))),
% 1.94/0.62    inference(cnf_transformation,[],[f46])).
% 1.94/0.62  fof(f188,plain,(
% 1.94/0.62    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl5_1),
% 1.94/0.62    inference(resolution,[],[f186,f123])).
% 1.94/0.62  fof(f123,plain,(
% 1.94/0.62    ~r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | spl5_1),
% 1.94/0.62    inference(avatar_component_clause,[],[f121])).
% 1.94/0.62  fof(f121,plain,(
% 1.94/0.62    spl5_1 <=> r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.94/0.62  fof(f186,plain,(
% 1.94/0.62    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.94/0.62    inference(resolution,[],[f76,f59])).
% 1.94/0.62  fof(f76,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f31])).
% 1.94/0.62  fof(f31,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f30])).
% 1.94/0.62  fof(f30,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f18])).
% 1.94/0.62  fof(f18,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.94/0.62  fof(f204,plain,(
% 1.94/0.62    spl5_5),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f203])).
% 1.94/0.62  fof(f203,plain,(
% 1.94/0.62    $false | spl5_5),
% 1.94/0.62    inference(resolution,[],[f193,f59])).
% 1.94/0.62  fof(f193,plain,(
% 1.94/0.62    ~v1_relat_1(sK2) | spl5_5),
% 1.94/0.62    inference(avatar_component_clause,[],[f191])).
% 1.94/0.62  fof(f202,plain,(
% 1.94/0.62    ~spl5_5 | ~spl5_6 | spl5_7),
% 1.94/0.62    inference(avatar_split_clause,[],[f189,f199,f195,f191])).
% 1.94/0.62  fof(f189,plain,(
% 1.94/0.62    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.94/0.62    inference(superposition,[],[f186,f67])).
% 1.94/0.62  fof(f67,plain,(
% 1.94/0.62    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f26])).
% 1.94/0.62  fof(f26,plain,(
% 1.94/0.62    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.94/0.62    inference(ennf_transformation,[],[f13])).
% 1.94/0.62  fof(f13,axiom,(
% 1.94/0.62    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.94/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.94/0.62  fof(f129,plain,(
% 1.94/0.62    ~spl5_2 | ~spl5_1),
% 1.94/0.62    inference(avatar_split_clause,[],[f115,f121,f125])).
% 1.94/0.62  fof(f115,plain,(
% 1.94/0.62    ~r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)),
% 1.94/0.62    inference(extensionality_resolution,[],[f81,f63])).
% 1.94/0.62  fof(f63,plain,(
% 1.94/0.62    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.94/0.62    inference(cnf_transformation,[],[f46])).
% 1.94/0.62  % SZS output end Proof for theBenchmark
% 1.94/0.62  % (3431)------------------------------
% 1.94/0.62  % (3431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.62  % (3431)Termination reason: Refutation
% 1.94/0.62  
% 1.94/0.62  % (3431)Memory used [KB]: 7164
% 1.94/0.62  % (3431)Time elapsed: 0.193 s
% 1.94/0.62  % (3431)------------------------------
% 1.94/0.62  % (3431)------------------------------
% 1.94/0.62  % (3418)Success in time 0.253 s
%------------------------------------------------------------------------------
