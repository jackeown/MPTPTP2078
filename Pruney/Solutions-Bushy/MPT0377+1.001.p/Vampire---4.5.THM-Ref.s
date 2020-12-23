%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0377+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 191 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  479 (1073 expanded)
%              Number of equality atoms :  175 ( 267 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f189,f258,f331,f368,f373,f392,f1024,f1026,f1027,f1028,f1029,f1030])).

fof(f1030,plain,
    ( sK5 != sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ m1_subset_1(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1029,plain,
    ( sK4 != sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ m1_subset_1(sK4,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1028,plain,
    ( sK3 != sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ m1_subset_1(sK3,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1027,plain,
    ( sK2 != sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1026,plain,
    ( sK1 != sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1024,plain,
    ( spl9_23
    | spl9_24
    | spl9_25
    | spl9_26
    | spl9_27
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f992,f370,f1021,f1017,f1013,f1009,f1005])).

fof(f1005,plain,
    ( spl9_23
  <=> sK1 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f1009,plain,
    ( spl9_24
  <=> sK2 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f1013,plain,
    ( spl9_25
  <=> sK3 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f1017,plain,
    ( spl9_26
  <=> sK4 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f1021,plain,
    ( spl9_27
  <=> sK5 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f370,plain,
    ( spl9_21
  <=> r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f992,plain,
    ( sK5 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK4 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK3 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK2 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK1 = sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl9_21 ),
    inference(resolution,[],[f372,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X4)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X4
              & sK8(X0,X1,X2,X3,X4,X5) != X3
              & sK8(X0,X1,X2,X3,X4,X5) != X2
              & sK8(X0,X1,X2,X3,X4,X5) != X1
              & sK8(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK8(X0,X1,X2,X3,X4,X5) = X4
            | sK8(X0,X1,X2,X3,X4,X5) = X3
            | sK8(X0,X1,X2,X3,X4,X5) = X2
            | sK8(X0,X1,X2,X3,X4,X5) = X1
            | sK8(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f34])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X4
            & sK8(X0,X1,X2,X3,X4,X5) != X3
            & sK8(X0,X1,X2,X3,X4,X5) != X2
            & sK8(X0,X1,X2,X3,X4,X5) != X1
            & sK8(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK8(X0,X1,X2,X3,X4,X5) = X4
          | sK8(X0,X1,X2,X3,X4,X5) = X3
          | sK8(X0,X1,X2,X3,X4,X5) = X2
          | sK8(X0,X1,X2,X3,X4,X5) = X1
          | sK8(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f372,plain,
    ( r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f370])).

fof(f392,plain,
    ( ~ spl9_22
    | spl9_10
    | spl9_20 ),
    inference(avatar_split_clause,[],[f379,f365,f186,f389])).

fof(f389,plain,
    ( spl9_22
  <=> m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f186,plain,
    ( spl9_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f365,plain,
    ( spl9_20
  <=> r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f379,plain,
    ( ~ m1_subset_1(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | spl9_10
    | spl9_20 ),
    inference(unit_resulting_resolution,[],[f188,f367,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f367,plain,
    ( ~ r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f365])).

fof(f188,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f373,plain,
    ( spl9_21
    | spl9_19 ),
    inference(avatar_split_clause,[],[f353,f327,f370])).

fof(f327,plain,
    ( spl9_19
  <=> r1_tarski(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f353,plain,
    ( r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))
    | spl9_19 ),
    inference(unit_resulting_resolution,[],[f329,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f329,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f327])).

fof(f368,plain,
    ( ~ spl9_20
    | spl9_19 ),
    inference(avatar_split_clause,[],[f354,f327,f365])).

fof(f354,plain,
    ( ~ r2_hidden(sK6(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | spl9_19 ),
    inference(unit_resulting_resolution,[],[f329,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f331,plain,
    ( ~ spl9_19
    | spl9_16 ),
    inference(avatar_split_clause,[],[f315,f255,f327])).

fof(f255,plain,
    ( spl9_16
  <=> r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f315,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | spl9_16 ),
    inference(resolution,[],[f257,f68])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f257,plain,
    ( ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | spl9_16 ),
    inference(avatar_component_clause,[],[f255])).

fof(f258,plain,
    ( ~ spl9_16
    | spl9_1 ),
    inference(avatar_split_clause,[],[f253,f82,f255])).

fof(f82,plain,
    ( spl9_1
  <=> m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f253,plain,
    ( ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f243,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f243,plain,
    ( ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl9_1 ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f189,plain,
    ( ~ spl9_10
    | spl9_2 ),
    inference(avatar_split_clause,[],[f116,f87,f186])).

fof(f87,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f89,f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f89,plain,
    ( k1_xboole_0 != sK0
    | spl9_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f115,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f36,f112])).

fof(f112,plain,
    ( spl9_7
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK5,sK0)
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f20,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(sK1,X2,X3,X4,X5),k1_zfmisc_1(sK0))
                      & k1_xboole_0 != sK0
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
                    ( ~ m1_subset_1(k3_enumset1(sK1,X2,X3,X4,X5),k1_zfmisc_1(sK0))
                    & k1_xboole_0 != sK0
                    & m1_subset_1(X5,sK0) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ m1_subset_1(k3_enumset1(sK1,sK2,X3,X4,X5),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X5,sK0) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ m1_subset_1(k3_enumset1(sK1,sK2,X3,X4,X5),k1_zfmisc_1(sK0))
                & k1_xboole_0 != sK0
                & m1_subset_1(X5,sK0) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,X4,X5),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X5,sK0) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,X4,X5),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X5,sK0) )
        & m1_subset_1(X4,sK0) )
   => ( ? [X5] :
          ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X5,sK0) )
   => ( ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
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
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
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
                       => ( k1_xboole_0 != X0
                         => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
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
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).

fof(f110,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f37,f107])).

fof(f107,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f37,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f38,f102])).

fof(f102,plain,
    ( spl9_5
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f38,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f39,f97])).

fof(f97,plain,
    ( spl9_4
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f39,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f40,f92])).

fof(f92,plain,
    ( spl9_3
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f40,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
