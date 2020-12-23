%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t42_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 316 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   23
%              Number of atoms          :  381 (1525 expanded)
%              Number of equality atoms :   40 ( 160 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1463,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f129,f133,f137,f138,f1321,f1396,f1462])).

fof(f1462,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1461])).

fof(f1461,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f124,f1447])).

fof(f1447,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1341,f136])).

fof(f136,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_6
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1341,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f268,f128])).

fof(f128,plain,
    ( k1_ordinal1(sK1) = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_4
  <=> k1_ordinal1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f268,plain,(
    ! [X0] :
      ( ~ v4_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f267,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',fc2_ordinal1)).

fof(f267,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v4_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f266,f87])).

fof(f87,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t10_ordinal1)).

fof(f266,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v4_ordinal1(k1_ordinal1(X0))
      | ~ r2_hidden(X0,k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v4_ordinal1(k1_ordinal1(X0))
      | ~ r2_hidden(X0,k1_ordinal1(X0))
      | ~ v3_ordinal1(X0)
      | ~ v4_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f230,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f71,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t41_ordinal1)).

fof(f230,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v4_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f94,f162])).

fof(f162,plain,(
    ! [X0] : ~ r2_hidden(k1_ordinal1(X0),X0) ),
    inference(resolution,[],[f106,f87])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',antisymmetry_r2_hidden)).

fof(f124,plain,
    ( v4_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1396,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1395])).

fof(f1395,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1394,f136])).

fof(f1394,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1341,f1319])).

fof(f1319,plain,
    ( v4_ordinal1(sK0)
    | ~ spl4_0 ),
    inference(subsumption_resolution,[],[f1318,f79])).

fof(f79,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ( ( v4_ordinal1(sK0)
        & k1_ordinal1(sK1) = sK0
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK1) = X0
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t42_ordinal1)).

fof(f1318,plain,
    ( ~ v3_ordinal1(sK0)
    | v4_ordinal1(sK0)
    | ~ spl4_0 ),
    inference(equality_resolution,[],[f1272])).

fof(f1272,plain,
    ( ! [X12] :
        ( sK0 != X12
        | ~ v3_ordinal1(X12)
        | v4_ordinal1(X12) )
    | ~ spl4_0 ),
    inference(subsumption_resolution,[],[f1220,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1220,plain,
    ( ! [X12] :
        ( sK0 != X12
        | ~ v3_ordinal1(sK2(X12))
        | ~ v3_ordinal1(X12)
        | v4_ordinal1(X12) )
    | ~ spl4_0 ),
    inference(superposition,[],[f121,f853])).

fof(f853,plain,(
    ! [X1] :
      ( k1_ordinal1(sK2(X1)) = X1
      | ~ v3_ordinal1(X1)
      | v4_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f852,f95])).

fof(f852,plain,(
    ! [X1] :
      ( k1_ordinal1(sK2(X1)) = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(sK2(X1))
      | v4_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f850,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f850,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(X1),X1)
      | k1_ordinal1(sK2(X1)) = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(sK2(X1))
      | v4_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f811])).

fof(f811,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(X1),X1)
      | k1_ordinal1(sK2(X1)) = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(sK2(X1))
      | v4_ordinal1(X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f440,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f440,plain,(
    ! [X2,X1] :
      ( r2_hidden(k1_ordinal1(X1),X2)
      | ~ r2_hidden(X1,X2)
      | k1_ordinal1(X1) = X2
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f439,f157])).

fof(f157,plain,(
    ! [X0] :
      ( v1_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f93,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',cc1_ordinal1)).

fof(f439,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,X2)
      | k1_ordinal1(X1) = X2
      | ~ v3_ordinal1(X2)
      | r2_hidden(k1_ordinal1(X1),X2)
      | ~ v1_ordinal1(k1_ordinal1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,X2)
      | k1_ordinal1(X1) = X2
      | ~ v3_ordinal1(X2)
      | r2_hidden(k1_ordinal1(X1),X2)
      | ~ v3_ordinal1(X2)
      | ~ v1_ordinal1(k1_ordinal1(X1)) ) ),
    inference(resolution,[],[f287,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t21_ordinal1)).

fof(f287,plain,(
    ! [X8,X9] :
      ( r2_xboole_0(k1_ordinal1(X9),X8)
      | ~ v3_ordinal1(X9)
      | ~ r2_hidden(X9,X8)
      | k1_ordinal1(X9) = X8
      | ~ v3_ordinal1(X8) ) ),
    inference(resolution,[],[f206,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',d8_xboole_0)).

fof(f206,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f205,f93])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f98,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',redefinition_r1_ordinal1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t33_ordinal1)).

fof(f121,plain,
    ( ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) )
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_0
  <=> ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f1321,plain,
    ( ~ spl4_0
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1319,f132])).

fof(f132,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_3
  <=> ~ v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f138,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f80,f135,f131])).

fof(f80,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f137,plain,
    ( spl4_0
    | spl4_6 ),
    inference(avatar_split_clause,[],[f81,f135,f120])).

fof(f81,plain,(
    ! [X2] :
      ( v3_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f133,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f82,f127,f131])).

fof(f82,plain,
    ( k1_ordinal1(sK1) = sK0
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f129,plain,
    ( spl4_0
    | spl4_4 ),
    inference(avatar_split_clause,[],[f83,f127,f120])).

fof(f83,plain,(
    ! [X2] :
      ( k1_ordinal1(sK1) = sK0
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,
    ( spl4_0
    | spl4_2 ),
    inference(avatar_split_clause,[],[f85,f123,f120])).

fof(f85,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
