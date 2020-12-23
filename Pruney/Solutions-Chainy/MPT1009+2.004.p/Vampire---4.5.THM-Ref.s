%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:26 EST 2020

% Result     : Theorem 2.57s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 300 expanded)
%              Number of leaves         :   43 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  572 ( 897 expanded)
%              Number of equality atoms :  122 ( 185 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f156,f161,f166,f174,f179,f197,f211,f251,f377,f405,f411,f679,f978,f2772,f2777,f2863,f3055,f3064,f3088,f3100])).

fof(f3100,plain,
    ( ~ spl8_10
    | spl8_35
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f2834,f676,f2545,f194])).

fof(f194,plain,
    ( spl8_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f2545,plain,
    ( spl8_35
  <=> r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f676,plain,
    ( spl8_26
  <=> r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f2834,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl8_26 ),
    inference(superposition,[],[f677,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f101,f102])).

fof(f102,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f677,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f676])).

fof(f3088,plain,
    ( ~ spl8_10
    | spl8_25
    | spl8_37
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f3075,f2545,f2580,f672,f194])).

fof(f672,plain,
    ( spl8_25
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f2580,plain,
    ( spl8_37
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f3075,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)
    | r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_35 ),
    inference(superposition,[],[f2546,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f2546,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f2545])).

fof(f3064,plain,(
    spl8_55 ),
    inference(avatar_contradiction_clause,[],[f3057])).

fof(f3057,plain,
    ( $false
    | spl8_55 ),
    inference(unit_resulting_resolution,[],[f94,f3054,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3054,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl8_55 ),
    inference(avatar_component_clause,[],[f3052])).

fof(f3052,plain,
    ( spl8_55
  <=> r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3055,plain,
    ( ~ spl8_55
    | spl8_21
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f2864,f2860,f408,f3052])).

fof(f408,plain,
    ( spl8_21
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f2860,plain,
    ( spl8_42
  <=> k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f2864,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl8_21
    | ~ spl8_42 ),
    inference(superposition,[],[f410,f2862])).

fof(f2862,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f2860])).

fof(f410,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl8_21 ),
    inference(avatar_component_clause,[],[f408])).

fof(f2863,plain,
    ( spl8_42
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f2838,f2580,f2860])).

fof(f2838,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2)
    | ~ spl8_37 ),
    inference(resolution,[],[f2581,f213])).

fof(f213,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f77,f181])).

fof(f181,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f70,f94])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2581,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f2777,plain,
    ( ~ spl8_1
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_29
    | spl8_37 ),
    inference(avatar_contradiction_clause,[],[f2773])).

fof(f2773,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_29
    | spl8_37 ),
    inference(unit_resulting_resolution,[],[f140,f196,f2582,f895,f766])).

fof(f766,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k9_relat_1(X2,X3),k1_xboole_0)
        | ~ v1_relat_1(X2)
        | ~ v4_relat_1(X2,k1_xboole_0)
        | ~ v1_funct_1(X2) )
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f749])).

fof(f749,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k9_relat_1(X2,X3),k1_xboole_0)
        | ~ v1_relat_1(X2)
        | ~ v4_relat_1(X2,k1_xboole_0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl8_20 ),
    inference(superposition,[],[f351,f746])).

fof(f746,plain,
    ( ! [X6] :
        ( k1_xboole_0 = k9_relat_1(X6,k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6) )
    | ~ spl8_20 ),
    inference(resolution,[],[f562,f404])).

fof(f404,plain,
    ( ! [X8] : ~ r2_hidden(X8,k1_xboole_0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl8_20
  <=> ! [X8] : ~ r2_hidden(X8,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f562,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK4(X8,k1_xboole_0,X9),X9)
        | k9_relat_1(X8,k1_xboole_0) = X9
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X8) )
    | ~ spl8_20 ),
    inference(resolution,[],[f85,f404])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | k9_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f351,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f78,f234])).

fof(f234,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_xboole_0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f213,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

fof(f895,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f894])).

fof(f894,plain,
    ( spl8_29
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f2582,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f196,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f140,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2772,plain,
    ( ~ spl8_10
    | ~ spl8_14
    | spl8_28
    | spl8_26 ),
    inference(avatar_split_clause,[],[f2771,f676,f888,f248,f194])).

fof(f248,plain,
    ( spl8_14
  <=> v4_relat_1(sK3,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f888,plain,
    ( spl8_28
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f2771,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK3)
    | spl8_26 ),
    inference(duplicate_literal_removal,[],[f2764])).

fof(f2764,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_26 ),
    inference(resolution,[],[f2542,f78])).

fof(f2542,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(X0)))
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ v4_relat_1(X0,k2_tarski(sK0,sK0))
        | ~ v1_relat_1(X0) )
    | spl8_26 ),
    inference(superposition,[],[f678,f393])).

fof(f393,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k2_tarski(X3,X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k2_tarski(X3,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f119,f103])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f72,f102,f102])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f678,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0)))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f676])).

fof(f978,plain,
    ( ~ spl8_10
    | spl8_29
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f963,f888,f894,f194])).

fof(f963,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28 ),
    inference(superposition,[],[f238,f890])).

fof(f890,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f888])).

fof(f238,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f104,f123])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f679,plain,
    ( ~ spl8_10
    | ~ spl8_1
    | ~ spl8_25
    | ~ spl8_26
    | spl8_21 ),
    inference(avatar_split_clause,[],[f668,f408,f676,f672,f138,f194])).

fof(f668,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_21 ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_21 ),
    inference(superposition,[],[f410,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f411,plain,
    ( ~ spl8_4
    | ~ spl8_21
    | spl8_8 ),
    inference(avatar_split_clause,[],[f406,f176,f408,f153])).

fof(f153,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f176,plain,
    ( spl8_8
  <=> r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f406,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | spl8_8 ),
    inference(superposition,[],[f178,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f178,plain,
    ( ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f405,plain,
    ( ~ spl8_7
    | spl8_20
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f401,f375,f158,f403,f170])).

fof(f170,plain,
    ( spl8_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f158,plain,
    ( spl8_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f375,plain,
    ( spl8_19
  <=> ! [X6] : r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f401,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f400,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f400,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_19 ),
    inference(trivial_inequality_removal,[],[f399])).

fof(f399,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X8,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_19 ),
    inference(superposition,[],[f92,f383])).

fof(f383,plain,
    ( ! [X5] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X5)
    | ~ spl8_19 ),
    inference(resolution,[],[f376,f213])).

fof(f376,plain,
    ( ! [X6] : r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f375])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f377,plain,
    ( ~ spl8_7
    | spl8_19
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f361,f209,f375,f170])).

fof(f209,plain,
    ( spl8_11
  <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f361,plain,
    ( ! [X6] :
        ( r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_11 ),
    inference(superposition,[],[f210,f120])).

fof(f210,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f251,plain,
    ( spl8_14
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f242,f153,f248])).

fof(f242,plain,
    ( v4_relat_1(sK3,k2_tarski(sK0,sK0))
    | ~ spl8_4 ),
    inference(resolution,[],[f112,f155])).

fof(f155,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f211,plain,
    ( ~ spl8_7
    | spl8_11
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f200,f163,f209,f170])).

fof(f163,plain,
    ( spl8_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f200,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_6 ),
    inference(superposition,[],[f105,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f197,plain,
    ( spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f188,f153,f194])).

fof(f188,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f98,f155])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f179,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f114,f176])).

fof(f114,plain,(
    ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f69,f102,f102])).

fof(f69,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f174,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f168,f170])).

fof(f168,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f100,f131])).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f96,f163])).

fof(f96,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f161,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f95,f158])).

fof(f95,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f115,f153])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f67,f102])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f65,f138])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (1801)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (1824)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (1816)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (1809)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (1810)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (1825)Refutation not found, incomplete strategy% (1825)------------------------------
% 0.22/0.53  % (1825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1825)Memory used [KB]: 10874
% 0.22/0.53  % (1825)Time elapsed: 0.120 s
% 0.22/0.53  % (1825)------------------------------
% 0.22/0.53  % (1825)------------------------------
% 0.22/0.53  % (1819)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (1797)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (1811)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (1820)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (1824)Refutation not found, incomplete strategy% (1824)------------------------------
% 0.22/0.54  % (1824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1824)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1824)Memory used [KB]: 6268
% 0.22/0.54  % (1824)Time elapsed: 0.122 s
% 0.22/0.54  % (1824)------------------------------
% 0.22/0.54  % (1824)------------------------------
% 0.22/0.54  % (1798)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (1800)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (1802)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1796)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (1795)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (1821)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (1815)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (1822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (1806)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (1818)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (1814)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (1803)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.56  % (1808)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.56  % (1807)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (1804)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.56  % (1817)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.56  % (1813)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.57  % (1823)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (1813)Refutation not found, incomplete strategy% (1813)------------------------------
% 1.48/0.57  % (1813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (1813)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (1813)Memory used [KB]: 10746
% 1.48/0.57  % (1813)Time elapsed: 0.150 s
% 1.48/0.57  % (1813)------------------------------
% 1.48/0.57  % (1813)------------------------------
% 1.48/0.57  % (1812)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.57  % (1826)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.57  % (1826)Refutation not found, incomplete strategy% (1826)------------------------------
% 1.48/0.57  % (1826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (1826)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (1826)Memory used [KB]: 1791
% 1.48/0.57  % (1826)Time elapsed: 0.154 s
% 1.48/0.57  % (1826)------------------------------
% 1.48/0.57  % (1826)------------------------------
% 1.48/0.58  % (1807)Refutation not found, incomplete strategy% (1807)------------------------------
% 1.48/0.58  % (1807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (1807)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (1807)Memory used [KB]: 10874
% 1.68/0.59  % (1807)Time elapsed: 0.150 s
% 1.68/0.59  % (1807)------------------------------
% 1.68/0.59  % (1807)------------------------------
% 2.16/0.67  % (1872)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.68  % (1876)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.69  % (1897)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.70  % (1888)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.71  % (1890)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.57/0.74  % (1820)Refutation found. Thanks to Tanya!
% 2.57/0.74  % SZS status Theorem for theBenchmark
% 2.57/0.76  % SZS output start Proof for theBenchmark
% 2.95/0.76  fof(f3101,plain,(
% 2.95/0.76    $false),
% 2.95/0.76    inference(avatar_sat_refutation,[],[f141,f156,f161,f166,f174,f179,f197,f211,f251,f377,f405,f411,f679,f978,f2772,f2777,f2863,f3055,f3064,f3088,f3100])).
% 2.95/0.76  fof(f3100,plain,(
% 2.95/0.76    ~spl8_10 | spl8_35 | ~spl8_26),
% 2.95/0.76    inference(avatar_split_clause,[],[f2834,f676,f2545,f194])).
% 2.95/0.76  fof(f194,plain,(
% 2.95/0.76    spl8_10 <=> v1_relat_1(sK3)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.95/0.76  fof(f2545,plain,(
% 2.95/0.76    spl8_35 <=> r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 2.95/0.76  fof(f676,plain,(
% 2.95/0.76    spl8_26 <=> r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0)))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 2.95/0.76  fof(f2834,plain,(
% 2.95/0.76    r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_relat_1(sK3) | ~spl8_26),
% 2.95/0.76    inference(superposition,[],[f677,f120])).
% 2.95/0.76  fof(f120,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 2.95/0.76    inference(definition_unfolding,[],[f101,f102])).
% 2.95/0.76  fof(f102,plain,(
% 2.95/0.76    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f3])).
% 2.95/0.76  fof(f3,axiom,(
% 2.95/0.76    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.95/0.76  fof(f101,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f39])).
% 2.95/0.76  fof(f39,plain,(
% 2.95/0.76    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.95/0.76    inference(ennf_transformation,[],[f10])).
% 2.95/0.76  fof(f10,axiom,(
% 2.95/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 2.95/0.76  fof(f677,plain,(
% 2.95/0.76    r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0))) | ~spl8_26),
% 2.95/0.76    inference(avatar_component_clause,[],[f676])).
% 2.95/0.76  fof(f3088,plain,(
% 2.95/0.76    ~spl8_10 | spl8_25 | spl8_37 | ~spl8_35),
% 2.95/0.76    inference(avatar_split_clause,[],[f3075,f2545,f2580,f672,f194])).
% 2.95/0.76  fof(f672,plain,(
% 2.95/0.76    spl8_25 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 2.95/0.76  fof(f2580,plain,(
% 2.95/0.76    spl8_37 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 2.95/0.76  fof(f3075,plain,(
% 2.95/0.76    r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) | r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl8_35),
% 2.95/0.76    inference(superposition,[],[f2546,f93])).
% 2.95/0.76  fof(f93,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f58])).
% 2.95/0.76  fof(f58,plain,(
% 2.95/0.76    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(nnf_transformation,[],[f33])).
% 2.95/0.76  fof(f33,plain,(
% 2.95/0.76    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(ennf_transformation,[],[f15])).
% 2.95/0.76  fof(f15,axiom,(
% 2.95/0.76    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 2.95/0.76  fof(f2546,plain,(
% 2.95/0.76    r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) | ~spl8_35),
% 2.95/0.76    inference(avatar_component_clause,[],[f2545])).
% 2.95/0.76  fof(f3064,plain,(
% 2.95/0.76    spl8_55),
% 2.95/0.76    inference(avatar_contradiction_clause,[],[f3057])).
% 2.95/0.76  fof(f3057,plain,(
% 2.95/0.76    $false | spl8_55),
% 2.95/0.76    inference(unit_resulting_resolution,[],[f94,f3054,f70])).
% 2.95/0.76  fof(f70,plain,(
% 2.95/0.76    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f45])).
% 2.95/0.76  fof(f45,plain,(
% 2.95/0.76    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.95/0.76    inference(nnf_transformation,[],[f8])).
% 2.95/0.76  fof(f8,axiom,(
% 2.95/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.95/0.76  fof(f3054,plain,(
% 2.95/0.76    ~r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl8_55),
% 2.95/0.76    inference(avatar_component_clause,[],[f3052])).
% 2.95/0.76  fof(f3052,plain,(
% 2.95/0.76    spl8_55 <=> r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 2.95/0.76  fof(f94,plain,(
% 2.95/0.76    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.95/0.76    inference(cnf_transformation,[],[f7])).
% 2.95/0.76  fof(f7,axiom,(
% 2.95/0.76    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.95/0.76  fof(f3055,plain,(
% 2.95/0.76    ~spl8_55 | spl8_21 | ~spl8_42),
% 2.95/0.76    inference(avatar_split_clause,[],[f2864,f2860,f408,f3052])).
% 2.95/0.76  fof(f408,plain,(
% 2.95/0.76    spl8_21 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 2.95/0.76  fof(f2860,plain,(
% 2.95/0.76    spl8_42 <=> k1_xboole_0 = k9_relat_1(sK3,sK2)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 2.95/0.76  fof(f2864,plain,(
% 2.95/0.76    ~r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (spl8_21 | ~spl8_42)),
% 2.95/0.76    inference(superposition,[],[f410,f2862])).
% 2.95/0.76  fof(f2862,plain,(
% 2.95/0.76    k1_xboole_0 = k9_relat_1(sK3,sK2) | ~spl8_42),
% 2.95/0.76    inference(avatar_component_clause,[],[f2860])).
% 2.95/0.76  fof(f410,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl8_21),
% 2.95/0.76    inference(avatar_component_clause,[],[f408])).
% 2.95/0.76  fof(f2863,plain,(
% 2.95/0.76    spl8_42 | ~spl8_37),
% 2.95/0.76    inference(avatar_split_clause,[],[f2838,f2580,f2860])).
% 2.95/0.76  fof(f2838,plain,(
% 2.95/0.76    k1_xboole_0 = k9_relat_1(sK3,sK2) | ~spl8_37),
% 2.95/0.76    inference(resolution,[],[f2581,f213])).
% 2.95/0.76  fof(f213,plain,(
% 2.95/0.76    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 2.95/0.76    inference(resolution,[],[f77,f181])).
% 2.95/0.76  fof(f181,plain,(
% 2.95/0.76    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.95/0.76    inference(resolution,[],[f70,f94])).
% 2.95/0.76  fof(f77,plain,(
% 2.95/0.76    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f49])).
% 2.95/0.76  fof(f49,plain,(
% 2.95/0.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/0.76    inference(flattening,[],[f48])).
% 2.95/0.76  fof(f48,plain,(
% 2.95/0.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/0.76    inference(nnf_transformation,[],[f1])).
% 2.95/0.76  fof(f1,axiom,(
% 2.95/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.95/0.76  fof(f2581,plain,(
% 2.95/0.76    r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) | ~spl8_37),
% 2.95/0.76    inference(avatar_component_clause,[],[f2580])).
% 2.95/0.76  fof(f2777,plain,(
% 2.95/0.76    ~spl8_1 | ~spl8_10 | ~spl8_20 | ~spl8_29 | spl8_37),
% 2.95/0.76    inference(avatar_contradiction_clause,[],[f2773])).
% 2.95/0.76  fof(f2773,plain,(
% 2.95/0.76    $false | (~spl8_1 | ~spl8_10 | ~spl8_20 | ~spl8_29 | spl8_37)),
% 2.95/0.76    inference(unit_resulting_resolution,[],[f140,f196,f2582,f895,f766])).
% 2.95/0.76  fof(f766,plain,(
% 2.95/0.76    ( ! [X2,X3] : (r1_tarski(k9_relat_1(X2,X3),k1_xboole_0) | ~v1_relat_1(X2) | ~v4_relat_1(X2,k1_xboole_0) | ~v1_funct_1(X2)) ) | ~spl8_20),
% 2.95/0.76    inference(duplicate_literal_removal,[],[f749])).
% 2.95/0.76  fof(f749,plain,(
% 2.95/0.76    ( ! [X2,X3] : (r1_tarski(k9_relat_1(X2,X3),k1_xboole_0) | ~v1_relat_1(X2) | ~v4_relat_1(X2,k1_xboole_0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl8_20),
% 2.95/0.76    inference(superposition,[],[f351,f746])).
% 2.95/0.76  fof(f746,plain,(
% 2.95/0.76    ( ! [X6] : (k1_xboole_0 = k9_relat_1(X6,k1_xboole_0) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) ) | ~spl8_20),
% 2.95/0.76    inference(resolution,[],[f562,f404])).
% 2.95/0.76  fof(f404,plain,(
% 2.95/0.76    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0)) ) | ~spl8_20),
% 2.95/0.76    inference(avatar_component_clause,[],[f403])).
% 2.95/0.76  fof(f403,plain,(
% 2.95/0.76    spl8_20 <=> ! [X8] : ~r2_hidden(X8,k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 2.95/0.76  fof(f562,plain,(
% 2.95/0.76    ( ! [X8,X9] : (r2_hidden(sK4(X8,k1_xboole_0,X9),X9) | k9_relat_1(X8,k1_xboole_0) = X9 | ~v1_funct_1(X8) | ~v1_relat_1(X8)) ) | ~spl8_20),
% 2.95/0.76    inference(resolution,[],[f85,f404])).
% 2.95/0.76  fof(f85,plain,(
% 2.95/0.76    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | k9_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f55])).
% 2.95/0.76  fof(f55,plain,(
% 2.95/0.76    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).
% 2.95/0.76  fof(f52,plain,(
% 2.95/0.76    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.95/0.76    introduced(choice_axiom,[])).
% 2.95/0.76  fof(f53,plain,(
% 2.95/0.76    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))))),
% 2.95/0.76    introduced(choice_axiom,[])).
% 2.95/0.76  fof(f54,plain,(
% 2.95/0.76    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))))),
% 2.95/0.76    introduced(choice_axiom,[])).
% 2.95/0.76  fof(f51,plain,(
% 2.95/0.76    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.76    inference(rectify,[],[f50])).
% 2.95/0.76  fof(f50,plain,(
% 2.95/0.76    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.76    inference(nnf_transformation,[],[f31])).
% 2.95/0.76  fof(f31,plain,(
% 2.95/0.76    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.76    inference(flattening,[],[f30])).
% 2.95/0.76  fof(f30,plain,(
% 2.95/0.76    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.95/0.76    inference(ennf_transformation,[],[f18])).
% 2.95/0.76  fof(f18,axiom,(
% 2.95/0.76    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 2.95/0.76  fof(f351,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0)) )),
% 2.95/0.76    inference(duplicate_literal_removal,[],[f344])).
% 2.95/0.76  fof(f344,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.95/0.76    inference(superposition,[],[f78,f234])).
% 2.95/0.76  fof(f234,plain,(
% 2.95/0.76    ( ! [X1] : (k1_xboole_0 = k1_relat_1(X1) | ~v4_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(resolution,[],[f213,f103])).
% 2.95/0.76  fof(f103,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f59])).
% 2.95/0.76  fof(f59,plain,(
% 2.95/0.76    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(nnf_transformation,[],[f40])).
% 2.95/0.76  fof(f40,plain,(
% 2.95/0.76    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(ennf_transformation,[],[f11])).
% 2.95/0.76  fof(f11,axiom,(
% 2.95/0.76    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.95/0.76  fof(f78,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f27])).
% 2.95/0.76  fof(f27,plain,(
% 2.95/0.76    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(ennf_transformation,[],[f14])).
% 2.95/0.76  fof(f14,axiom,(
% 2.95/0.76    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
% 2.95/0.76  fof(f895,plain,(
% 2.95/0.76    v4_relat_1(sK3,k1_xboole_0) | ~spl8_29),
% 2.95/0.76    inference(avatar_component_clause,[],[f894])).
% 2.95/0.76  fof(f894,plain,(
% 2.95/0.76    spl8_29 <=> v4_relat_1(sK3,k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 2.95/0.76  fof(f2582,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) | spl8_37),
% 2.95/0.76    inference(avatar_component_clause,[],[f2580])).
% 2.95/0.76  fof(f196,plain,(
% 2.95/0.76    v1_relat_1(sK3) | ~spl8_10),
% 2.95/0.76    inference(avatar_component_clause,[],[f194])).
% 2.95/0.76  fof(f140,plain,(
% 2.95/0.76    v1_funct_1(sK3) | ~spl8_1),
% 2.95/0.76    inference(avatar_component_clause,[],[f138])).
% 2.95/0.76  fof(f138,plain,(
% 2.95/0.76    spl8_1 <=> v1_funct_1(sK3)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.95/0.76  fof(f2772,plain,(
% 2.95/0.76    ~spl8_10 | ~spl8_14 | spl8_28 | spl8_26),
% 2.95/0.76    inference(avatar_split_clause,[],[f2771,f676,f888,f248,f194])).
% 2.95/0.76  fof(f248,plain,(
% 2.95/0.76    spl8_14 <=> v4_relat_1(sK3,k2_tarski(sK0,sK0))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 2.95/0.76  fof(f888,plain,(
% 2.95/0.76    spl8_28 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 2.95/0.76  fof(f2771,plain,(
% 2.95/0.76    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k2_tarski(sK0,sK0)) | ~v1_relat_1(sK3) | spl8_26),
% 2.95/0.76    inference(duplicate_literal_removal,[],[f2764])).
% 2.95/0.76  fof(f2764,plain,(
% 2.95/0.76    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k2_tarski(sK0,sK0)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | spl8_26),
% 2.95/0.76    inference(resolution,[],[f2542,f78])).
% 2.95/0.76  fof(f2542,plain,(
% 2.95/0.76    ( ! [X0] : (~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(X0))) | k1_xboole_0 = k1_relat_1(X0) | ~v4_relat_1(X0,k2_tarski(sK0,sK0)) | ~v1_relat_1(X0)) ) | spl8_26),
% 2.95/0.76    inference(superposition,[],[f678,f393])).
% 2.95/0.76  fof(f393,plain,(
% 2.95/0.76    ( ! [X2,X3] : (k1_relat_1(X2) = k2_tarski(X3,X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k2_tarski(X3,X3)) | ~v1_relat_1(X2)) )),
% 2.95/0.76    inference(resolution,[],[f119,f103])).
% 2.95/0.76  fof(f119,plain,(
% 2.95/0.76    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 2.95/0.76    inference(definition_unfolding,[],[f72,f102,f102])).
% 2.95/0.76  fof(f72,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.95/0.76    inference(cnf_transformation,[],[f47])).
% 2.95/0.76  fof(f47,plain,(
% 2.95/0.76    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.95/0.76    inference(flattening,[],[f46])).
% 2.95/0.76  fof(f46,plain,(
% 2.95/0.76    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.95/0.76    inference(nnf_transformation,[],[f5])).
% 2.95/0.76  fof(f5,axiom,(
% 2.95/0.76    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.95/0.76  fof(f678,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0))) | spl8_26),
% 2.95/0.76    inference(avatar_component_clause,[],[f676])).
% 2.95/0.76  fof(f978,plain,(
% 2.95/0.76    ~spl8_10 | spl8_29 | ~spl8_28),
% 2.95/0.76    inference(avatar_split_clause,[],[f963,f888,f894,f194])).
% 2.95/0.76  fof(f963,plain,(
% 2.95/0.76    v4_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | ~spl8_28),
% 2.95/0.76    inference(superposition,[],[f238,f890])).
% 2.95/0.76  fof(f890,plain,(
% 2.95/0.76    k1_xboole_0 = k1_relat_1(sK3) | ~spl8_28),
% 2.95/0.76    inference(avatar_component_clause,[],[f888])).
% 2.95/0.76  fof(f238,plain,(
% 2.95/0.76    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.95/0.76    inference(resolution,[],[f104,f123])).
% 2.95/0.76  fof(f123,plain,(
% 2.95/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.95/0.76    inference(equality_resolution,[],[f76])).
% 2.95/0.76  fof(f76,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.95/0.76    inference(cnf_transformation,[],[f49])).
% 2.95/0.76  fof(f104,plain,(
% 2.95/0.76    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f59])).
% 2.95/0.76  fof(f679,plain,(
% 2.95/0.76    ~spl8_10 | ~spl8_1 | ~spl8_25 | ~spl8_26 | spl8_21),
% 2.95/0.76    inference(avatar_split_clause,[],[f668,f408,f676,f672,f138,f194])).
% 2.95/0.76  fof(f668,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl8_21),
% 2.95/0.76    inference(duplicate_literal_removal,[],[f654])).
% 2.95/0.76  fof(f654,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl8_21),
% 2.95/0.76    inference(superposition,[],[f410,f79])).
% 2.95/0.76  fof(f79,plain,(
% 2.95/0.76    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f29])).
% 2.95/0.76  fof(f29,plain,(
% 2.95/0.76    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.95/0.76    inference(flattening,[],[f28])).
% 2.95/0.76  fof(f28,plain,(
% 2.95/0.76    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.95/0.76    inference(ennf_transformation,[],[f19])).
% 2.95/0.76  fof(f19,axiom,(
% 2.95/0.76    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 2.95/0.76  fof(f411,plain,(
% 2.95/0.76    ~spl8_4 | ~spl8_21 | spl8_8),
% 2.95/0.76    inference(avatar_split_clause,[],[f406,f176,f408,f153])).
% 2.95/0.76  fof(f153,plain,(
% 2.95/0.76    spl8_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.95/0.76  fof(f176,plain,(
% 2.95/0.76    spl8_8 <=> r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.95/0.76  fof(f406,plain,(
% 2.95/0.76    ~r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) | spl8_8),
% 2.95/0.76    inference(superposition,[],[f178,f88])).
% 2.95/0.76  fof(f88,plain,(
% 2.95/0.76    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/0.76    inference(cnf_transformation,[],[f32])).
% 2.95/0.76  fof(f32,plain,(
% 2.95/0.76    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.76    inference(ennf_transformation,[],[f22])).
% 2.95/0.76  fof(f22,axiom,(
% 2.95/0.76    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.95/0.76  fof(f178,plain,(
% 2.95/0.76    ~r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl8_8),
% 2.95/0.76    inference(avatar_component_clause,[],[f176])).
% 2.95/0.76  fof(f405,plain,(
% 2.95/0.76    ~spl8_7 | spl8_20 | ~spl8_5 | ~spl8_19),
% 2.95/0.76    inference(avatar_split_clause,[],[f401,f375,f158,f403,f170])).
% 2.95/0.76  fof(f170,plain,(
% 2.95/0.76    spl8_7 <=> v1_relat_1(k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.95/0.76  fof(f158,plain,(
% 2.95/0.76    spl8_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.95/0.76  fof(f375,plain,(
% 2.95/0.76    spl8_19 <=> ! [X6] : r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 2.95/0.76  fof(f401,plain,(
% 2.95/0.76    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl8_5 | ~spl8_19)),
% 2.95/0.76    inference(forward_demodulation,[],[f400,f160])).
% 2.95/0.76  fof(f160,plain,(
% 2.95/0.76    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_5),
% 2.95/0.76    inference(avatar_component_clause,[],[f158])).
% 2.95/0.76  fof(f400,plain,(
% 2.95/0.76    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_19),
% 2.95/0.76    inference(trivial_inequality_removal,[],[f399])).
% 2.95/0.76  fof(f399,plain,(
% 2.95/0.76    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X8,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_19),
% 2.95/0.76    inference(superposition,[],[f92,f383])).
% 2.95/0.76  fof(f383,plain,(
% 2.95/0.76    ( ! [X5] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X5)) ) | ~spl8_19),
% 2.95/0.76    inference(resolution,[],[f376,f213])).
% 2.95/0.76  fof(f376,plain,(
% 2.95/0.76    ( ! [X6] : (r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0)) ) | ~spl8_19),
% 2.95/0.76    inference(avatar_component_clause,[],[f375])).
% 2.95/0.76  fof(f92,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f58])).
% 2.95/0.76  fof(f377,plain,(
% 2.95/0.76    ~spl8_7 | spl8_19 | ~spl8_11),
% 2.95/0.76    inference(avatar_split_clause,[],[f361,f209,f375,f170])).
% 2.95/0.76  fof(f209,plain,(
% 2.95/0.76    spl8_11 <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.95/0.76  fof(f361,plain,(
% 2.95/0.76    ( ! [X6] : (r1_tarski(k11_relat_1(k1_xboole_0,X6),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_11),
% 2.95/0.76    inference(superposition,[],[f210,f120])).
% 2.95/0.76  fof(f210,plain,(
% 2.95/0.76    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl8_11),
% 2.95/0.76    inference(avatar_component_clause,[],[f209])).
% 2.95/0.76  fof(f251,plain,(
% 2.95/0.76    spl8_14 | ~spl8_4),
% 2.95/0.76    inference(avatar_split_clause,[],[f242,f153,f248])).
% 2.95/0.76  fof(f242,plain,(
% 2.95/0.76    v4_relat_1(sK3,k2_tarski(sK0,sK0)) | ~spl8_4),
% 2.95/0.76    inference(resolution,[],[f112,f155])).
% 2.95/0.76  fof(f155,plain,(
% 2.95/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) | ~spl8_4),
% 2.95/0.76    inference(avatar_component_clause,[],[f153])).
% 2.95/0.76  fof(f112,plain,(
% 2.95/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f42])).
% 2.95/0.76  fof(f42,plain,(
% 2.95/0.76    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.76    inference(ennf_transformation,[],[f21])).
% 2.95/0.76  fof(f21,axiom,(
% 2.95/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.95/0.76  fof(f211,plain,(
% 2.95/0.76    ~spl8_7 | spl8_11 | ~spl8_6),
% 2.95/0.76    inference(avatar_split_clause,[],[f200,f163,f209,f170])).
% 2.95/0.76  fof(f163,plain,(
% 2.95/0.76    spl8_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.95/0.76    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.95/0.76  fof(f200,plain,(
% 2.95/0.76    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_6),
% 2.95/0.76    inference(superposition,[],[f105,f165])).
% 2.95/0.76  fof(f165,plain,(
% 2.95/0.76    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_6),
% 2.95/0.76    inference(avatar_component_clause,[],[f163])).
% 2.95/0.76  fof(f105,plain,(
% 2.95/0.76    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f41])).
% 2.95/0.76  fof(f41,plain,(
% 2.95/0.76    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.95/0.76    inference(ennf_transformation,[],[f13])).
% 2.95/0.76  fof(f13,axiom,(
% 2.95/0.76    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 2.95/0.76  fof(f197,plain,(
% 2.95/0.76    spl8_10 | ~spl8_4),
% 2.95/0.76    inference(avatar_split_clause,[],[f188,f153,f194])).
% 2.95/0.76  fof(f188,plain,(
% 2.95/0.76    v1_relat_1(sK3) | ~spl8_4),
% 2.95/0.76    inference(resolution,[],[f98,f155])).
% 2.95/0.76  fof(f98,plain,(
% 2.95/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.95/0.76    inference(cnf_transformation,[],[f36])).
% 2.95/0.76  fof(f36,plain,(
% 2.95/0.76    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.76    inference(ennf_transformation,[],[f20])).
% 2.95/0.76  fof(f20,axiom,(
% 2.95/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.95/0.76  fof(f179,plain,(
% 2.95/0.76    ~spl8_8),
% 2.95/0.76    inference(avatar_split_clause,[],[f114,f176])).
% 2.95/0.76  fof(f114,plain,(
% 2.95/0.76    ~r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.95/0.76    inference(definition_unfolding,[],[f69,f102,f102])).
% 2.95/0.76  fof(f69,plain,(
% 2.95/0.76    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.95/0.76    inference(cnf_transformation,[],[f44])).
% 2.95/0.76  fof(f44,plain,(
% 2.95/0.76    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 2.95/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f43])).
% 2.95/0.76  fof(f43,plain,(
% 2.95/0.76    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 2.95/0.76    introduced(choice_axiom,[])).
% 2.95/0.76  fof(f26,plain,(
% 2.95/0.76    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.95/0.76    inference(flattening,[],[f25])).
% 2.95/0.76  fof(f25,plain,(
% 2.95/0.76    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.95/0.76    inference(ennf_transformation,[],[f24])).
% 2.95/0.76  fof(f24,negated_conjecture,(
% 2.95/0.76    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.95/0.76    inference(negated_conjecture,[],[f23])).
% 2.95/0.76  fof(f23,conjecture,(
% 2.95/0.76    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.95/0.76  fof(f174,plain,(
% 2.95/0.76    spl8_7),
% 2.95/0.76    inference(avatar_split_clause,[],[f168,f170])).
% 2.95/0.76  fof(f168,plain,(
% 2.95/0.76    v1_relat_1(k1_xboole_0)),
% 2.95/0.76    inference(superposition,[],[f100,f131])).
% 2.95/0.76  fof(f131,plain,(
% 2.95/0.76    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.95/0.76    inference(equality_resolution,[],[f90])).
% 2.95/0.76  fof(f90,plain,(
% 2.95/0.76    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.95/0.76    inference(cnf_transformation,[],[f57])).
% 2.95/0.76  fof(f57,plain,(
% 2.95/0.76    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.95/0.76    inference(flattening,[],[f56])).
% 2.95/0.76  fof(f56,plain,(
% 2.95/0.76    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.95/0.76    inference(nnf_transformation,[],[f6])).
% 2.95/0.76  fof(f6,axiom,(
% 2.95/0.76    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.95/0.76  fof(f100,plain,(
% 2.95/0.76    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.95/0.76    inference(cnf_transformation,[],[f12])).
% 2.95/0.76  fof(f12,axiom,(
% 2.95/0.76    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.95/0.76  fof(f166,plain,(
% 2.95/0.76    spl8_6),
% 2.95/0.76    inference(avatar_split_clause,[],[f96,f163])).
% 2.95/0.76  fof(f96,plain,(
% 2.95/0.76    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.95/0.76    inference(cnf_transformation,[],[f16])).
% 2.95/0.76  fof(f16,axiom,(
% 2.95/0.76    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.95/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.95/0.76  fof(f161,plain,(
% 2.95/0.76    spl8_5),
% 2.95/0.76    inference(avatar_split_clause,[],[f95,f158])).
% 2.95/0.76  fof(f95,plain,(
% 2.95/0.76    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.95/0.76    inference(cnf_transformation,[],[f16])).
% 2.95/0.76  fof(f156,plain,(
% 2.95/0.76    spl8_4),
% 2.95/0.76    inference(avatar_split_clause,[],[f115,f153])).
% 2.95/0.76  fof(f115,plain,(
% 2.95/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))),
% 2.95/0.76    inference(definition_unfolding,[],[f67,f102])).
% 2.95/0.76  fof(f67,plain,(
% 2.95/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.95/0.76    inference(cnf_transformation,[],[f44])).
% 2.95/0.76  fof(f141,plain,(
% 2.95/0.76    spl8_1),
% 2.95/0.76    inference(avatar_split_clause,[],[f65,f138])).
% 2.95/0.76  fof(f65,plain,(
% 2.95/0.76    v1_funct_1(sK3)),
% 2.95/0.76    inference(cnf_transformation,[],[f44])).
% 2.95/0.76  % SZS output end Proof for theBenchmark
% 2.95/0.76  % (1820)------------------------------
% 2.95/0.76  % (1820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.76  % (1820)Termination reason: Refutation
% 2.95/0.76  
% 2.95/0.76  % (1820)Memory used [KB]: 13048
% 2.95/0.76  % (1820)Time elapsed: 0.305 s
% 2.95/0.76  % (1820)------------------------------
% 2.95/0.76  % (1820)------------------------------
% 2.95/0.77  % (1794)Success in time 0.392 s
%------------------------------------------------------------------------------
