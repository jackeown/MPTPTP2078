%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0380+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 266 expanded)
%              Number of leaves         :   50 ( 150 expanded)
%              Depth                    :   10
%              Number of atoms          :  653 (2123 expanded)
%              Number of equality atoms :  262 ( 453 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1884,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f306,f408,f499,f554,f559,f637,f1874,f1876,f1877,f1878,f1879,f1880,f1881,f1882,f1883])).

fof(f1883,plain,
    ( sK8 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK8,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1882,plain,
    ( sK7 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK7,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1881,plain,
    ( sK6 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK6,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1880,plain,
    ( sK5 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1879,plain,
    ( sK4 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK4,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1878,plain,
    ( sK3 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK3,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1877,plain,
    ( sK2 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1876,plain,
    ( sK1 != sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1874,plain,
    ( spl12_29
    | spl12_30
    | spl12_31
    | spl12_32
    | spl12_33
    | spl12_34
    | spl12_35
    | spl12_36
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f1827,f556,f1871,f1867,f1863,f1859,f1855,f1851,f1847,f1843])).

fof(f1843,plain,
    ( spl12_29
  <=> sK1 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f1847,plain,
    ( spl12_30
  <=> sK2 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f1851,plain,
    ( spl12_31
  <=> sK3 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f1855,plain,
    ( spl12_32
  <=> sK4 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f1859,plain,
    ( spl12_33
  <=> sK5 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f1863,plain,
    ( spl12_34
  <=> sK6 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f1867,plain,
    ( spl12_35
  <=> sK7 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f1871,plain,
    ( spl12_36
  <=> sK8 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f556,plain,
    ( spl12_27
  <=> r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f1827,plain,
    ( sK8 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK7 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK6 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK5 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK4 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK3 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK2 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK1 = sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl12_27 ),
    inference(resolution,[],[f558,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] :
      ( X7 = X10
      | X6 = X10
      | X5 = X10
      | X4 = X10
      | X3 = X10
      | X2 = X10
      | X1 = X10
      | X0 = X10
      | ~ r2_hidden(X10,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( X7 = X10
      | X6 = X10
      | X5 = X10
      | X4 = X10
      | X3 = X10
      | X2 = X10
      | X1 = X10
      | X0 = X10
      | ~ r2_hidden(X10,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ( ( ( sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
            | ~ r2_hidden(sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | r2_hidden(sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f36,f37])).

fof(f37,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
          | ~ r2_hidden(sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | r2_hidden(sK11(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f558,plain,
    ( r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f556])).

fof(f637,plain,
    ( ~ spl12_28
    | spl12_13
    | spl12_26 ),
    inference(avatar_split_clause,[],[f621,f551,f303,f634])).

fof(f634,plain,
    ( spl12_28
  <=> m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f303,plain,
    ( spl12_13
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f551,plain,
    ( spl12_26
  <=> r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f621,plain,
    ( ~ m1_subset_1(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | spl12_13
    | spl12_26 ),
    inference(unit_resulting_resolution,[],[f305,f553,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f553,plain,
    ( ~ r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | spl12_26 ),
    inference(avatar_component_clause,[],[f551])).

fof(f305,plain,
    ( ~ v1_xboole_0(sK0)
    | spl12_13 ),
    inference(avatar_component_clause,[],[f303])).

fof(f559,plain,
    ( spl12_27
    | spl12_25 ),
    inference(avatar_split_clause,[],[f536,f495,f556])).

fof(f495,plain,
    ( spl12_25
  <=> r1_tarski(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f536,plain,
    ( r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | spl12_25 ),
    inference(unit_resulting_resolution,[],[f497,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f497,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | spl12_25 ),
    inference(avatar_component_clause,[],[f495])).

fof(f554,plain,
    ( ~ spl12_26
    | spl12_25 ),
    inference(avatar_split_clause,[],[f537,f495,f551])).

fof(f537,plain,
    ( ~ r2_hidden(sK9(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | spl12_25 ),
    inference(unit_resulting_resolution,[],[f497,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f499,plain,
    ( ~ spl12_25
    | spl12_22 ),
    inference(avatar_split_clause,[],[f480,f405,f495])).

fof(f405,plain,
    ( spl12_22
  <=> r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f480,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | spl12_22 ),
    inference(resolution,[],[f407,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK10(X0,X1),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r1_tarski(sK10(X0,X1),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK10(X0,X1),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( r1_tarski(sK10(X0,X1),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f407,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | spl12_22 ),
    inference(avatar_component_clause,[],[f405])).

fof(f408,plain,
    ( ~ spl12_22
    | spl12_1 ),
    inference(avatar_split_clause,[],[f403,f100,f405])).

fof(f100,plain,
    ( spl12_1
  <=> m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f403,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | spl12_1 ),
    inference(subsumption_resolution,[],[f390,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f390,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl12_1 ),
    inference(resolution,[],[f102,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f102,plain,
    ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f306,plain,
    ( ~ spl12_13
    | spl12_2 ),
    inference(avatar_split_clause,[],[f149,f105,f303])).

fof(f105,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f149,plain,
    ( ~ v1_xboole_0(sK0)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f107,plain,
    ( k1_xboole_0 != sK0
    | spl12_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f148,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f39,f145])).

fof(f145,plain,
    ( spl12_10
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f39,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK8,sK0)
    & m1_subset_1(sK7,sK0)
    & m1_subset_1(sK6,sK0)
    & m1_subset_1(sK5,sK0)
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f10,f23,f22,f21,f20,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ? [X8] :
                                    ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                    & k1_xboole_0 != X0
                                    & m1_subset_1(X8,X0) )
                                & m1_subset_1(X7,X0) )
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(sK1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                                  & k1_xboole_0 != sK0
                                  & m1_subset_1(X8,sK0) )
                              & m1_subset_1(X7,sK0) )
                          & m1_subset_1(X6,sK0) )
                      & m1_subset_1(X5,sK0) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ? [X8] :
                                ( ~ m1_subset_1(k6_enumset1(sK1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                                & k1_xboole_0 != sK0
                                & m1_subset_1(X8,sK0) )
                            & m1_subset_1(X7,sK0) )
                        & m1_subset_1(X6,sK0) )
                    & m1_subset_1(X5,sK0) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ? [X8] :
                              ( ~ m1_subset_1(k6_enumset1(sK1,sK2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                              & k1_xboole_0 != sK0
                              & m1_subset_1(X8,sK0) )
                          & m1_subset_1(X7,sK0) )
                      & m1_subset_1(X6,sK0) )
                  & m1_subset_1(X5,sK0) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ? [X8] :
                            ( ~ m1_subset_1(k6_enumset1(sK1,sK2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                            & k1_xboole_0 != sK0
                            & m1_subset_1(X8,sK0) )
                        & m1_subset_1(X7,sK0) )
                    & m1_subset_1(X6,sK0) )
                & m1_subset_1(X5,sK0) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                          & k1_xboole_0 != sK0
                          & m1_subset_1(X8,sK0) )
                      & m1_subset_1(X7,sK0) )
                  & m1_subset_1(X6,sK0) )
              & m1_subset_1(X5,sK0) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,X4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                        & k1_xboole_0 != sK0
                        & m1_subset_1(X8,sK0) )
                    & m1_subset_1(X7,sK0) )
                & m1_subset_1(X6,sK0) )
            & m1_subset_1(X5,sK0) )
        & m1_subset_1(X4,sK0) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                      & k1_xboole_0 != sK0
                      & m1_subset_1(X8,sK0) )
                  & m1_subset_1(X7,sK0) )
              & m1_subset_1(X6,sK0) )
          & m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,X5,X6,X7,X8),k1_zfmisc_1(sK0))
                    & k1_xboole_0 != sK0
                    & m1_subset_1(X8,sK0) )
                & m1_subset_1(X7,sK0) )
            & m1_subset_1(X6,sK0) )
        & m1_subset_1(X5,sK0) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,X6,X7,X8),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X8,sK0) )
              & m1_subset_1(X7,sK0) )
          & m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,X6,X7,X8),k1_zfmisc_1(sK0))
                & k1_xboole_0 != sK0
                & m1_subset_1(X8,sK0) )
            & m1_subset_1(X7,sK0) )
        & m1_subset_1(X6,sK0) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,X7,X8),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X8,sK0) )
          & m1_subset_1(X7,sK0) )
      & m1_subset_1(sK6,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,X7,X8),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X8,sK0) )
        & m1_subset_1(X7,sK0) )
   => ( ? [X8] :
          ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,X8),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X8,sK0) )
      & m1_subset_1(sK7,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X8] :
        ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,X8),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X8,sK0) )
   => ( ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK8,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ! [X8] :
                                    ( m1_subset_1(X8,X0)
                                   => ( k1_xboole_0 != X0
                                     => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_subset_1)).

fof(f143,plain,(
    spl12_9 ),
    inference(avatar_split_clause,[],[f40,f140])).

fof(f140,plain,
    ( spl12_9
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f40,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f41,f135])).

fof(f135,plain,
    ( spl12_8
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f41,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f42,f130])).

fof(f130,plain,
    ( spl12_7
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f42,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f43,f125])).

fof(f125,plain,
    ( spl12_6
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f43,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f44,f120])).

fof(f120,plain,
    ( spl12_5
  <=> m1_subset_1(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f44,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f45,f115])).

fof(f115,plain,
    ( spl12_4
  <=> m1_subset_1(sK7,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f45,plain,(
    m1_subset_1(sK7,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f110,plain,
    ( spl12_3
  <=> m1_subset_1(sK8,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f46,plain,(
    m1_subset_1(sK8,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,(
    ~ spl12_2 ),
    inference(avatar_split_clause,[],[f47,f105])).

fof(f47,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
