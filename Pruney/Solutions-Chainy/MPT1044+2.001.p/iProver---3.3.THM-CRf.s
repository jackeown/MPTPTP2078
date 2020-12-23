%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:49 EST 2020

% Result     : Theorem 43.42s
% Output     : CNFRefutation 43.42s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 207 expanded)
%              Number of clauses        :   54 (  62 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  550 ( 761 expanded)
%              Number of equality atoms :   61 (  90 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(k3_partfun1(o_0_0_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f95,f64])).

fof(f41,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f54,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f54])).

fof(f58,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK6(X0,X1,X2,X7))
        & v1_partfun1(sK6(X0,X1,X2,X7),X1)
        & sK6(X0,X1,X2,X7) = X7
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK6(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X3))
        & v1_partfun1(sK5(X0,X1,X2,X3),X1)
        & sK5(X0,X1,X2,X3) = X4
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK4(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK4(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK4(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X3))
              & v1_partfun1(sK5(X0,X1,X2,X3),X1)
              & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
              & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK5(X0,X1,X2,X3)) )
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK6(X0,X1,X2,X7))
                & v1_partfun1(sK6(X0,X1,X2,X7),X1)
                & sK6(X0,X1,X2,X7) = X7
                & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK6(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).

fof(f81,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f107,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f81])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f28,f42,f41])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,
    ( ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1)
   => k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f40,f60])).

fof(f100,plain,(
    k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,(
    k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
    inference(definition_unfolding,[],[f100,f64])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f51,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f20])).

fof(f69,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    v1_funct_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f68,f64])).

cnf(c_8,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_126296,plain,
    ( v1_partfun1(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,X1)))
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_134347,plain,
    ( v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
    | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_126296])).

cnf(c_32,plain,
    ( r1_partfun1(k3_partfun1(o_0_0_xboole_0,X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_126439,plain,
    ( r1_partfun1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
    | ~ v1_relat_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
    | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_121358,plain,
    ( ~ sP0(k3_partfun1(X0,X1,X2),X1,X2,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
    | ~ r1_partfun1(k3_partfun1(X0,X1,X2),X3)
    | ~ v1_partfun1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_125397,plain,
    ( ~ sP0(k3_partfun1(X0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(X0,sK7,sK8)))
    | ~ r1_partfun1(k3_partfun1(X0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
    | ~ v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
    | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(X0,sK7,sK8)))
    | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_121358])).

cnf(c_125399,plain,
    ( ~ sP0(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | ~ r1_partfun1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
    | ~ v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
    | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_125397])).

cnf(c_28,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_119669,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(k1_funct_2(X0,sK8))
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_122526,plain,
    ( v1_xboole_0(k1_funct_2(sK7,sK8))
    | ~ v1_xboole_0(sK8)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_119669])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_434,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_435,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_5228,plain,
    ( sP0(k3_partfun1(X0,X1,X2),X1,X2,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
    | ~ m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(X0,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_21477,plain,
    ( sP0(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | ~ m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_5228])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(sK3(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6789,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK3(X2,X0),X1)
    | r2_hidden(sK3(X2,X0),X2)
    | X0 = X2 ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_12352,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK3(X1,X0),X1)
    | X0 = X1 ),
    inference(factoring,[status(thm)],[c_6789])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6055,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_29])).

cnf(c_12368,plain,
    ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
    | v1_relat_1(sK3(k1_funct_2(X1,X2),X0))
    | X0 = k1_funct_2(X1,X2) ),
    inference(resolution,[status(thm)],[c_12352,c_6055])).

cnf(c_37,negated_conjecture,
    ( k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_13827,plain,
    ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
    | v1_relat_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
    inference(resolution,[status(thm)],[c_12368,c_37])).

cnf(c_26,plain,
    ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6747,plain,
    ( m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ v1_funct_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k5_partfun1(X1,X2,X0),k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5223,plain,
    ( ~ m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)),k1_funct_2(X1,X2))
    | ~ v1_funct_1(k3_partfun1(X0,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_6294,plain,
    ( ~ m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
    | ~ v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_5223])).

cnf(c_5575,plain,
    ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),X0)
    | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),X0)
    | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6293,plain,
    ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_5575])).

cnf(c_27,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_partfun1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6236,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0)
    | v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8))
    | ~ v1_funct_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_501,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(resolution,[status(thm)],[c_30,c_9])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_partfun1(X0,X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_31,c_30,c_29,c_9])).

cnf(c_506,plain,
    ( v1_partfun1(X0,X1)
    | ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_505])).

cnf(c_5370,plain,
    ( v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
    | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
    | v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_5371,plain,
    ( m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5372,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
    | v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | ~ r2_hidden(sK3(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5342,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
    | k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) = k1_funct_2(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5329,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
    | ~ v1_xboole_0(k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5183,plain,
    ( r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
    | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
    | k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) = k1_funct_2(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( v1_funct_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6,plain,
    ( v1_relat_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134347,c_126439,c_125399,c_122526,c_21477,c_13827,c_6747,c_6294,c_6293,c_6236,c_5370,c_5371,c_5372,c_5342,c_5329,c_5183,c_5,c_6,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:57:49 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 43.42/6.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.42/6.01  
% 43.42/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.42/6.01  
% 43.42/6.01  ------  iProver source info
% 43.42/6.01  
% 43.42/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.42/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.42/6.01  git: non_committed_changes: false
% 43.42/6.01  git: last_make_outside_of_git: false
% 43.42/6.01  
% 43.42/6.01  ------ 
% 43.42/6.01  ------ Parsing...
% 43.42/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.42/6.01  
% 43.42/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.42/6.01  
% 43.42/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.42/6.01  
% 43.42/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.42/6.01  ------ Proving...
% 43.42/6.01  ------ Problem Properties 
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  clauses                                 35
% 43.42/6.01  conjectures                             1
% 43.42/6.01  EPR                                     4
% 43.42/6.01  Horn                                    25
% 43.42/6.01  unary                                   3
% 43.42/6.01  binary                                  5
% 43.42/6.01  lits                                    105
% 43.42/6.01  lits eq                                 6
% 43.42/6.01  fd_pure                                 0
% 43.42/6.01  fd_pseudo                               0
% 43.42/6.01  fd_cond                                 0
% 43.42/6.01  fd_pseudo_cond                          3
% 43.42/6.01  AC symbols                              0
% 43.42/6.01  
% 43.42/6.01  ------ Input Options Time Limit: Unbounded
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  ------ 
% 43.42/6.01  Current options:
% 43.42/6.01  ------ 
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  ------ Proving...
% 43.42/6.01  
% 43.42/6.01  
% 43.42/6.01  % SZS status Theorem for theBenchmark.p
% 43.42/6.01  
% 43.42/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.42/6.01  
% 43.42/6.01  fof(f7,axiom,(
% 43.42/6.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 43.42/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.01  
% 43.42/6.01  fof(f24,plain,(
% 43.42/6.01    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 43.42/6.01    inference(ennf_transformation,[],[f7])).
% 43.42/6.01  
% 43.42/6.01  fof(f71,plain,(
% 43.42/6.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 43.42/6.01    inference(cnf_transformation,[],[f24])).
% 43.42/6.01  
% 43.42/6.01  fof(f13,axiom,(
% 43.42/6.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2))),
% 43.42/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.01  
% 43.42/6.01  fof(f34,plain,(
% 43.42/6.01    ! [X0,X1,X2] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 43.42/6.01    inference(ennf_transformation,[],[f13])).
% 43.42/6.01  
% 43.42/6.01  fof(f35,plain,(
% 43.42/6.01    ! [X0,X1,X2] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 43.42/6.01    inference(flattening,[],[f34])).
% 43.42/6.01  
% 43.42/6.01  fof(f95,plain,(
% 43.42/6.01    ( ! [X2,X0,X1] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 43.42/6.01    inference(cnf_transformation,[],[f35])).
% 43.42/6.01  
% 43.42/6.01  fof(f2,axiom,(
% 43.42/6.01    k1_xboole_0 = o_0_0_xboole_0),
% 43.42/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.01  
% 43.42/6.01  fof(f64,plain,(
% 43.42/6.01    k1_xboole_0 = o_0_0_xboole_0),
% 43.42/6.01    inference(cnf_transformation,[],[f2])).
% 43.42/6.01  
% 43.42/6.01  fof(f103,plain,(
% 43.42/6.01    ( ! [X2,X0,X1] : (r1_partfun1(k3_partfun1(o_0_0_xboole_0,X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 43.42/6.01    inference(definition_unfolding,[],[f95,f64])).
% 43.42/6.01  
% 43.42/6.01  fof(f41,plain,(
% 43.42/6.01    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 43.42/6.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 43.42/6.01  
% 43.42/6.01  fof(f54,plain,(
% 43.42/6.01    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 43.42/6.01    inference(nnf_transformation,[],[f41])).
% 43.42/6.01  
% 43.42/6.01  fof(f55,plain,(
% 43.42/6.01    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 43.42/6.01    inference(rectify,[],[f54])).
% 43.42/6.01  
% 43.42/6.01  fof(f58,plain,(
% 43.42/6.01    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X1) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK6(X0,X1,X2,X7))))),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f57,plain,(
% 43.42/6.02    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X1) & sK5(X0,X1,X2,X3) = X4 & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X3))))) )),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f56,plain,(
% 43.42/6.02    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK4(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f59,plain,(
% 43.42/6.02    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X3))) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X1) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK6(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 43.42/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).
% 43.42/6.02  
% 43.42/6.02  fof(f81,plain,(
% 43.42/6.02    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f59])).
% 43.42/6.02  
% 43.42/6.02  fof(f107,plain,(
% 43.42/6.02    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 43.42/6.02    inference(equality_resolution,[],[f81])).
% 43.42/6.02  
% 43.42/6.02  fof(f11,axiom,(
% 43.42/6.02    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f31,plain,(
% 43.42/6.02    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 43.42/6.02    inference(ennf_transformation,[],[f11])).
% 43.42/6.02  
% 43.42/6.02  fof(f32,plain,(
% 43.42/6.02    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 43.42/6.02    inference(flattening,[],[f31])).
% 43.42/6.02  
% 43.42/6.02  fof(f91,plain,(
% 43.42/6.02    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f32])).
% 43.42/6.02  
% 43.42/6.02  fof(f42,plain,(
% 43.42/6.02    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 43.42/6.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 43.42/6.02  
% 43.42/6.02  fof(f52,plain,(
% 43.42/6.02    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 43.42/6.02    inference(nnf_transformation,[],[f42])).
% 43.42/6.02  
% 43.42/6.02  fof(f53,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 43.42/6.02    inference(rectify,[],[f52])).
% 43.42/6.02  
% 43.42/6.02  fof(f74,plain,(
% 43.42/6.02    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f53])).
% 43.42/6.02  
% 43.42/6.02  fof(f105,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 43.42/6.02    inference(equality_resolution,[],[f74])).
% 43.42/6.02  
% 43.42/6.02  fof(f9,axiom,(
% 43.42/6.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f27,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 43.42/6.02    inference(ennf_transformation,[],[f9])).
% 43.42/6.02  
% 43.42/6.02  fof(f28,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 43.42/6.02    inference(flattening,[],[f27])).
% 43.42/6.02  
% 43.42/6.02  fof(f43,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 43.42/6.02    inference(definition_folding,[],[f28,f42,f41])).
% 43.42/6.02  
% 43.42/6.02  fof(f88,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f43])).
% 43.42/6.02  
% 43.42/6.02  fof(f3,axiom,(
% 43.42/6.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f18,plain,(
% 43.42/6.02    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.42/6.02    inference(unused_predicate_definition_removal,[],[f3])).
% 43.42/6.02  
% 43.42/6.02  fof(f21,plain,(
% 43.42/6.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 43.42/6.02    inference(ennf_transformation,[],[f18])).
% 43.42/6.02  
% 43.42/6.02  fof(f65,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f21])).
% 43.42/6.02  
% 43.42/6.02  fof(f4,axiom,(
% 43.42/6.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f22,plain,(
% 43.42/6.02    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 43.42/6.02    inference(ennf_transformation,[],[f4])).
% 43.42/6.02  
% 43.42/6.02  fof(f48,plain,(
% 43.42/6.02    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 43.42/6.02    inference(nnf_transformation,[],[f22])).
% 43.42/6.02  
% 43.42/6.02  fof(f49,plain,(
% 43.42/6.02    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f50,plain,(
% 43.42/6.02    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 43.42/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 43.42/6.02  
% 43.42/6.02  fof(f66,plain,(
% 43.42/6.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f50])).
% 43.42/6.02  
% 43.42/6.02  fof(f6,axiom,(
% 43.42/6.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f23,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.42/6.02    inference(ennf_transformation,[],[f6])).
% 43.42/6.02  
% 43.42/6.02  fof(f70,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.42/6.02    inference(cnf_transformation,[],[f23])).
% 43.42/6.02  
% 43.42/6.02  fof(f12,axiom,(
% 43.42/6.02    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f33,plain,(
% 43.42/6.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 43.42/6.02    inference(ennf_transformation,[],[f12])).
% 43.42/6.02  
% 43.42/6.02  fof(f94,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 43.42/6.02    inference(cnf_transformation,[],[f33])).
% 43.42/6.02  
% 43.42/6.02  fof(f16,conjecture,(
% 43.42/6.02    ! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1)),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f17,negated_conjecture,(
% 43.42/6.02    ~! [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_funct_2(X0,X1)),
% 43.42/6.02    inference(negated_conjecture,[],[f16])).
% 43.42/6.02  
% 43.42/6.02  fof(f40,plain,(
% 43.42/6.02    ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1)),
% 43.42/6.02    inference(ennf_transformation,[],[f17])).
% 43.42/6.02  
% 43.42/6.02  fof(f60,plain,(
% 43.42/6.02    ? [X0,X1] : k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k1_funct_2(X0,X1) => k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8)),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f61,plain,(
% 43.42/6.02    k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8)),
% 43.42/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f40,f60])).
% 43.42/6.02  
% 43.42/6.02  fof(f100,plain,(
% 43.42/6.02    k5_partfun1(sK7,sK8,k3_partfun1(k1_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8)),
% 43.42/6.02    inference(cnf_transformation,[],[f61])).
% 43.42/6.02  
% 43.42/6.02  fof(f104,plain,(
% 43.42/6.02    k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8)),
% 43.42/6.02    inference(definition_unfolding,[],[f100,f64])).
% 43.42/6.02  
% 43.42/6.02  fof(f10,axiom,(
% 43.42/6.02    ! [X0,X1,X2] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f29,plain,(
% 43.42/6.02    ! [X0,X1,X2] : ((m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 43.42/6.02    inference(ennf_transformation,[],[f10])).
% 43.42/6.02  
% 43.42/6.02  fof(f30,plain,(
% 43.42/6.02    ! [X0,X1,X2] : ((m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.42/6.02    inference(flattening,[],[f29])).
% 43.42/6.02  
% 43.42/6.02  fof(f90,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f30])).
% 43.42/6.02  
% 43.42/6.02  fof(f15,axiom,(
% 43.42/6.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f38,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 43.42/6.02    inference(ennf_transformation,[],[f15])).
% 43.42/6.02  
% 43.42/6.02  fof(f39,plain,(
% 43.42/6.02    ! [X0,X1,X2] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 43.42/6.02    inference(flattening,[],[f38])).
% 43.42/6.02  
% 43.42/6.02  fof(f99,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f39])).
% 43.42/6.02  
% 43.42/6.02  fof(f89,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (v1_funct_1(k3_partfun1(X0,X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f30])).
% 43.42/6.02  
% 43.42/6.02  fof(f93,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 43.42/6.02    inference(cnf_transformation,[],[f33])).
% 43.42/6.02  
% 43.42/6.02  fof(f8,axiom,(
% 43.42/6.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f25,plain,(
% 43.42/6.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 43.42/6.02    inference(ennf_transformation,[],[f8])).
% 43.42/6.02  
% 43.42/6.02  fof(f26,plain,(
% 43.42/6.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 43.42/6.02    inference(flattening,[],[f25])).
% 43.42/6.02  
% 43.42/6.02  fof(f73,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f26])).
% 43.42/6.02  
% 43.42/6.02  fof(f92,plain,(
% 43.42/6.02    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 43.42/6.02    inference(cnf_transformation,[],[f33])).
% 43.42/6.02  
% 43.42/6.02  fof(f67,plain,(
% 43.42/6.02    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f50])).
% 43.42/6.02  
% 43.42/6.02  fof(f1,axiom,(
% 43.42/6.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f44,plain,(
% 43.42/6.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 43.42/6.02    inference(nnf_transformation,[],[f1])).
% 43.42/6.02  
% 43.42/6.02  fof(f45,plain,(
% 43.42/6.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 43.42/6.02    inference(rectify,[],[f44])).
% 43.42/6.02  
% 43.42/6.02  fof(f46,plain,(
% 43.42/6.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 43.42/6.02    introduced(choice_axiom,[])).
% 43.42/6.02  
% 43.42/6.02  fof(f47,plain,(
% 43.42/6.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 43.42/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 43.42/6.02  
% 43.42/6.02  fof(f62,plain,(
% 43.42/6.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 43.42/6.02    inference(cnf_transformation,[],[f47])).
% 43.42/6.02  
% 43.42/6.02  fof(f5,axiom,(
% 43.42/6.02    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 43.42/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.42/6.02  
% 43.42/6.02  fof(f19,plain,(
% 43.42/6.02    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 43.42/6.02    inference(pure_predicate_removal,[],[f5])).
% 43.42/6.02  
% 43.42/6.02  fof(f20,plain,(
% 43.42/6.02    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 43.42/6.02    inference(pure_predicate_removal,[],[f19])).
% 43.42/6.02  
% 43.42/6.02  fof(f51,plain,(
% 43.42/6.02    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 43.42/6.02    inference(rectify,[],[f20])).
% 43.42/6.02  
% 43.42/6.02  fof(f69,plain,(
% 43.42/6.02    v1_funct_1(k1_xboole_0)),
% 43.42/6.02    inference(cnf_transformation,[],[f51])).
% 43.42/6.02  
% 43.42/6.02  fof(f101,plain,(
% 43.42/6.02    v1_funct_1(o_0_0_xboole_0)),
% 43.42/6.02    inference(definition_unfolding,[],[f69,f64])).
% 43.42/6.02  
% 43.42/6.02  fof(f68,plain,(
% 43.42/6.02    v1_relat_1(k1_xboole_0)),
% 43.42/6.02    inference(cnf_transformation,[],[f51])).
% 43.42/6.02  
% 43.42/6.02  fof(f102,plain,(
% 43.42/6.02    v1_relat_1(o_0_0_xboole_0)),
% 43.42/6.02    inference(definition_unfolding,[],[f68,f64])).
% 43.42/6.02  
% 43.42/6.02  cnf(c_8,plain,
% 43.42/6.02      ( v1_partfun1(X0,X1)
% 43.42/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ v1_xboole_0(X1) ),
% 43.42/6.02      inference(cnf_transformation,[],[f71]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_126296,plain,
% 43.42/6.02      ( v1_partfun1(X0,sK7)
% 43.42/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,X1)))
% 43.42/6.02      | ~ v1_xboole_0(sK7) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_8]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_134347,plain,
% 43.42/6.02      ( v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
% 43.42/6.02      | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | ~ v1_xboole_0(sK7) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_126296]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_32,plain,
% 43.42/6.02      ( r1_partfun1(k3_partfun1(o_0_0_xboole_0,X0,X1),X2)
% 43.42/6.02      | ~ v1_relat_1(X2)
% 43.42/6.02      | ~ v1_funct_1(X2) ),
% 43.42/6.02      inference(cnf_transformation,[],[f103]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_126439,plain,
% 43.42/6.02      ( r1_partfun1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
% 43.42/6.02      | ~ v1_relat_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
% 43.42/6.02      | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_32]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_19,plain,
% 43.42/6.02      ( ~ sP0(X0,X1,X2,X3)
% 43.42/6.02      | ~ r1_partfun1(X0,X4)
% 43.42/6.02      | ~ v1_partfun1(X4,X1)
% 43.42/6.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | r2_hidden(X4,X3)
% 43.42/6.02      | ~ v1_funct_1(X4) ),
% 43.42/6.02      inference(cnf_transformation,[],[f107]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_121358,plain,
% 43.42/6.02      ( ~ sP0(k3_partfun1(X0,X1,X2),X1,X2,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
% 43.42/6.02      | ~ r1_partfun1(k3_partfun1(X0,X1,X2),X3)
% 43.42/6.02      | ~ v1_partfun1(X3,X1)
% 43.42/6.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | r2_hidden(X3,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
% 43.42/6.02      | ~ v1_funct_1(X3) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_19]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_125397,plain,
% 43.42/6.02      ( ~ sP0(k3_partfun1(X0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(X0,sK7,sK8)))
% 43.42/6.02      | ~ r1_partfun1(k3_partfun1(X0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
% 43.42/6.02      | ~ v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
% 43.42/6.02      | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(X0,sK7,sK8)))
% 43.42/6.02      | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_121358]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_125399,plain,
% 43.42/6.02      ( ~ sP0(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | ~ r1_partfun1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))))
% 43.42/6.02      | ~ v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
% 43.42/6.02      | ~ m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | ~ v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_125397]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_28,plain,
% 43.42/6.02      ( ~ v1_xboole_0(X0)
% 43.42/6.02      | v1_xboole_0(X1)
% 43.42/6.02      | v1_xboole_0(k1_funct_2(X1,X0)) ),
% 43.42/6.02      inference(cnf_transformation,[],[f91]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_119669,plain,
% 43.42/6.02      ( v1_xboole_0(X0)
% 43.42/6.02      | v1_xboole_0(k1_funct_2(X0,sK8))
% 43.42/6.02      | ~ v1_xboole_0(sK8) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_28]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_122526,plain,
% 43.42/6.02      ( v1_xboole_0(k1_funct_2(sK7,sK8))
% 43.42/6.02      | ~ v1_xboole_0(sK8)
% 43.42/6.02      | v1_xboole_0(sK7) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_119669]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_12,plain,
% 43.42/6.02      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f105]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_25,plain,
% 43.42/6.02      ( sP1(X0,X1,X2)
% 43.42/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 43.42/6.02      | ~ v1_funct_1(X2) ),
% 43.42/6.02      inference(cnf_transformation,[],[f88]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_434,plain,
% 43.42/6.02      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 43.42/6.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 43.42/6.02      | ~ v1_funct_1(X3)
% 43.42/6.02      | X3 != X0
% 43.42/6.02      | X4 != X1
% 43.42/6.02      | X5 != X2 ),
% 43.42/6.02      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_435,plain,
% 43.42/6.02      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 43.42/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ v1_funct_1(X0) ),
% 43.42/6.02      inference(unflattening,[status(thm)],[c_434]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5228,plain,
% 43.42/6.02      ( sP0(k3_partfun1(X0,X1,X2),X1,X2,k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)))
% 43.42/6.02      | ~ m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ v1_funct_1(k3_partfun1(X0,X1,X2)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_435]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_21477,plain,
% 43.42/6.02      ( sP0(k3_partfun1(o_0_0_xboole_0,sK7,sK8),sK7,sK8,k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | ~ m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | ~ v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_5228]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_2,plain,
% 43.42/6.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 43.42/6.02      inference(cnf_transformation,[],[f65]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_4,plain,
% 43.42/6.02      ( r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X1 = X0 ),
% 43.42/6.02      inference(cnf_transformation,[],[f66]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6789,plain,
% 43.42/6.02      ( ~ r1_tarski(X0,X1)
% 43.42/6.02      | r2_hidden(sK3(X2,X0),X1)
% 43.42/6.02      | r2_hidden(sK3(X2,X0),X2)
% 43.42/6.02      | X0 = X2 ),
% 43.42/6.02      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_12352,plain,
% 43.42/6.02      ( ~ r1_tarski(X0,X1) | r2_hidden(sK3(X1,X0),X1) | X0 = X1 ),
% 43.42/6.02      inference(factoring,[status(thm)],[c_6789]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_7,plain,
% 43.42/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | v1_relat_1(X0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f70]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_29,plain,
% 43.42/6.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
% 43.42/6.02      inference(cnf_transformation,[],[f94]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6055,plain,
% 43.42/6.02      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | v1_relat_1(X0) ),
% 43.42/6.02      inference(resolution,[status(thm)],[c_7,c_29]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_12368,plain,
% 43.42/6.02      ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
% 43.42/6.02      | v1_relat_1(sK3(k1_funct_2(X1,X2),X0))
% 43.42/6.02      | X0 = k1_funct_2(X1,X2) ),
% 43.42/6.02      inference(resolution,[status(thm)],[c_12352,c_6055]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_37,negated_conjecture,
% 43.42/6.02      ( k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) != k1_funct_2(sK7,sK8) ),
% 43.42/6.02      inference(cnf_transformation,[],[f104]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_13827,plain,
% 43.42/6.02      ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
% 43.42/6.02      | v1_relat_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
% 43.42/6.02      inference(resolution,[status(thm)],[c_12368,c_37]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_26,plain,
% 43.42/6.02      ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ v1_relat_1(X0)
% 43.42/6.02      | ~ v1_funct_1(X0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f90]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6747,plain,
% 43.42/6.02      ( m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | ~ v1_relat_1(o_0_0_xboole_0)
% 43.42/6.02      | ~ v1_funct_1(o_0_0_xboole_0) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_26]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_36,plain,
% 43.42/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | r1_tarski(k5_partfun1(X1,X2,X0),k1_funct_2(X1,X2))
% 43.42/6.02      | ~ v1_funct_1(X0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f99]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5223,plain,
% 43.42/6.02      ( ~ m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | r1_tarski(k5_partfun1(X1,X2,k3_partfun1(X0,X1,X2)),k1_funct_2(X1,X2))
% 43.42/6.02      | ~ v1_funct_1(k3_partfun1(X0,X1,X2)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_36]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6294,plain,
% 43.42/6.02      ( ~ m1_subset_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
% 43.42/6.02      | ~ v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_5223]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5575,plain,
% 43.42/6.02      ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),X0)
% 43.42/6.02      | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),X0)
% 43.42/6.02      | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_2]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6293,plain,
% 43.42/6.02      ( ~ r1_tarski(k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)),k1_funct_2(sK7,sK8))
% 43.42/6.02      | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_5575]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_27,plain,
% 43.42/6.02      ( ~ v1_relat_1(X0)
% 43.42/6.02      | ~ v1_funct_1(X0)
% 43.42/6.02      | v1_funct_1(k3_partfun1(X0,X1,X2)) ),
% 43.42/6.02      inference(cnf_transformation,[],[f89]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6236,plain,
% 43.42/6.02      ( ~ v1_relat_1(o_0_0_xboole_0)
% 43.42/6.02      | v1_funct_1(k3_partfun1(o_0_0_xboole_0,sK7,sK8))
% 43.42/6.02      | ~ v1_funct_1(o_0_0_xboole_0) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_27]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_30,plain,
% 43.42/6.02      ( v1_funct_2(X0,X1,X2) | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
% 43.42/6.02      inference(cnf_transformation,[],[f93]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_9,plain,
% 43.42/6.02      ( ~ v1_funct_2(X0,X1,X2)
% 43.42/6.02      | v1_partfun1(X0,X1)
% 43.42/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ v1_funct_1(X0)
% 43.42/6.02      | v1_xboole_0(X2) ),
% 43.42/6.02      inference(cnf_transformation,[],[f73]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_501,plain,
% 43.42/6.02      ( v1_partfun1(X0,X1)
% 43.42/6.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.42/6.02      | ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 43.42/6.02      | ~ v1_funct_1(X0)
% 43.42/6.02      | v1_xboole_0(X2) ),
% 43.42/6.02      inference(resolution,[status(thm)],[c_30,c_9]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_31,plain,
% 43.42/6.02      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | v1_funct_1(X0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f92]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_505,plain,
% 43.42/6.02      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 43.42/6.02      | v1_partfun1(X0,X1)
% 43.42/6.02      | v1_xboole_0(X2) ),
% 43.42/6.02      inference(global_propositional_subsumption,
% 43.42/6.02                [status(thm)],
% 43.42/6.02                [c_501,c_31,c_30,c_29,c_9]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_506,plain,
% 43.42/6.02      ( v1_partfun1(X0,X1)
% 43.42/6.02      | ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 43.42/6.02      | v1_xboole_0(X2) ),
% 43.42/6.02      inference(renaming,[status(thm)],[c_505]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5370,plain,
% 43.42/6.02      ( v1_partfun1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),sK7)
% 43.42/6.02      | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
% 43.42/6.02      | v1_xboole_0(sK8) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_506]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5371,plain,
% 43.42/6.02      ( m1_subset_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 43.42/6.02      | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_29]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5372,plain,
% 43.42/6.02      ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
% 43.42/6.02      | v1_funct_1(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_31]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_3,plain,
% 43.42/6.02      ( ~ r2_hidden(sK3(X0,X1),X1)
% 43.42/6.02      | ~ r2_hidden(sK3(X0,X1),X0)
% 43.42/6.02      | X1 = X0 ),
% 43.42/6.02      inference(cnf_transformation,[],[f67]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5342,plain,
% 43.42/6.02      ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
% 43.42/6.02      | k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) = k1_funct_2(sK7,sK8) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_3]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_1,plain,
% 43.42/6.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 43.42/6.02      inference(cnf_transformation,[],[f62]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5329,plain,
% 43.42/6.02      ( ~ r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
% 43.42/6.02      | ~ v1_xboole_0(k1_funct_2(sK7,sK8)) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_1]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5183,plain,
% 43.42/6.02      ( r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)))
% 43.42/6.02      | r2_hidden(sK3(k1_funct_2(sK7,sK8),k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8))),k1_funct_2(sK7,sK8))
% 43.42/6.02      | k5_partfun1(sK7,sK8,k3_partfun1(o_0_0_xboole_0,sK7,sK8)) = k1_funct_2(sK7,sK8) ),
% 43.42/6.02      inference(instantiation,[status(thm)],[c_4]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_5,plain,
% 43.42/6.02      ( v1_funct_1(o_0_0_xboole_0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f101]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(c_6,plain,
% 43.42/6.02      ( v1_relat_1(o_0_0_xboole_0) ),
% 43.42/6.02      inference(cnf_transformation,[],[f102]) ).
% 43.42/6.02  
% 43.42/6.02  cnf(contradiction,plain,
% 43.42/6.02      ( $false ),
% 43.42/6.02      inference(minisat,
% 43.42/6.02                [status(thm)],
% 43.42/6.02                [c_134347,c_126439,c_125399,c_122526,c_21477,c_13827,
% 43.42/6.02                 c_6747,c_6294,c_6293,c_6236,c_5370,c_5371,c_5372,c_5342,
% 43.42/6.02                 c_5329,c_5183,c_5,c_6,c_37]) ).
% 43.42/6.02  
% 43.42/6.02  
% 43.42/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.42/6.02  
% 43.42/6.02  ------                               Statistics
% 43.42/6.02  
% 43.42/6.02  ------ Selected
% 43.42/6.02  
% 43.42/6.02  total_time:                             5.259
% 43.42/6.02  
%------------------------------------------------------------------------------
