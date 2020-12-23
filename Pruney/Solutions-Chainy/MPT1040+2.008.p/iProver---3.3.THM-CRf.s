%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:45 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 862 expanded)
%              Number of clauses        :   92 ( 260 expanded)
%              Number of leaves         :   23 ( 223 expanded)
%              Depth                    :   20
%              Number of atoms          :  626 (5918 expanded)
%              Number of equality atoms :  232 (1570 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(sK11,k5_partfun1(X0,X1,X2))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK11)
        & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK11,X0,X1)
        & v1_funct_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK8,sK9,sK10))
          & ( k1_xboole_0 = sK8
            | k1_xboole_0 != sK9 )
          & r1_partfun1(sK10,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
          & v1_funct_2(X3,sK8,sK9)
          & v1_funct_1(X3) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10))
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 != sK9 )
    & r1_partfun1(sK10,sK11)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK11,sK8,sK9)
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f22,f50,f49])).

fof(f90,plain,(
    v1_funct_2(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f51])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f10,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f23,plain,(
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

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f20,f24,f23])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X7))
        & v1_partfun1(sK7(X0,X1,X2,X7),X1)
        & sK7(X0,X1,X2,X7) = X7
        & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK7(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK6(X0,X1,X2,X3))
        & v1_partfun1(sK6(X0,X1,X2,X3),X1)
        & sK6(X0,X1,X2,X3) = X4
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
              | sK5(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK5(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK5(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK6(X0,X1,X2,X3))
              & v1_partfun1(sK6(X0,X1,X2,X3),X1)
              & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
              & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK6(X0,X1,X2,X3)) )
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK7(X0,X1,X2,X7))
                & v1_partfun1(sK7(X0,X1,X2,X7),X1)
                & sK7(X0,X1,X2,X7) = X7
                & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK7(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f47,f46,f45])).

fof(f77,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f77])).

fof(f87,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    r1_partfun1(sK10,sK11) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    ~ r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f34])).

fof(f58,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_497,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK9 != X2
    | sK8 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_498,plain,
    ( v1_partfun1(sK11,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK11)
    | v1_xboole_0(sK9) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_500,plain,
    ( v1_partfun1(sK11,sK8)
    | v1_xboole_0(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_40,c_38])).

cnf(c_7404,plain,
    ( v1_partfun1(sK11,sK8) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_7409,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_514,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X4 != X1
    | X3 != X0
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_515,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_7403,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7419,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10647,plain,
    ( sP0(X0,sK8,sK9,X1) != iProver_top
    | r1_partfun1(X0,sK11) != iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | r2_hidden(sK11,X1) = iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_7409,c_7419])).

cnf(c_45,plain,
    ( v1_funct_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11176,plain,
    ( r2_hidden(sK11,X1) = iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | r1_partfun1(X0,sK11) != iProver_top
    | sP0(X0,sK8,sK9,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10647,c_45])).

cnf(c_11177,plain,
    ( sP0(X0,sK8,sK9,X1) != iProver_top
    | r1_partfun1(X0,sK11) != iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | r2_hidden(sK11,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_11176])).

cnf(c_11186,plain,
    ( r1_partfun1(X0,sK11) != iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | r2_hidden(sK11,k5_partfun1(sK8,sK9,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7403,c_11177])).

cnf(c_11279,plain,
    ( r1_partfun1(sK11,sK11) != iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | r2_hidden(sK11,k5_partfun1(sK8,sK9,sK11)) = iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_7409,c_11186])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_37,negated_conjecture,
    ( r1_partfun1(sK10,sK11) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_48,plain,
    ( r1_partfun1(sK10,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_49,plain,
    ( r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7407,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_11280,plain,
    ( r1_partfun1(sK10,sK11) != iProver_top
    | v1_partfun1(sK11,sK8) != iProver_top
    | r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) = iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7407,c_11186])).

cnf(c_11439,plain,
    ( v1_partfun1(sK11,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11279,c_43,c_48,c_49,c_11280])).

cnf(c_11444,plain,
    ( v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_7404,c_11439])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7431,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11453,plain,
    ( sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11444,c_7431])).

cnf(c_12549,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11453,c_7409])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK9
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_12551,plain,
    ( sK8 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11453,c_36])).

cnf(c_12552,plain,
    ( sK8 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12551])).

cnf(c_12559,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12549,c_12552])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_12561,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12559,c_11])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9790,plain,
    ( ~ r2_hidden(sK3(X0,sK11),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9791,plain,
    ( r2_hidden(sK3(X0,sK11),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9790])).

cnf(c_9793,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK11),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9791])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7433,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7435,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8576,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7433,c_7435])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7413,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8171,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_7413])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7426,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8441,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8171,c_7426])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7429,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8667,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8441,c_7429])).

cnf(c_9076,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8576,c_8667])).

cnf(c_8596,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(X0))
    | r1_tarski(sK11,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8597,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK11,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8596])).

cnf(c_8599,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK11,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8597])).

cnf(c_6605,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8458,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(sK11,sK8)
    | sK8 != X1
    | sK11 != X0 ),
    inference(instantiation,[status(thm)],[c_6605])).

cnf(c_8459,plain,
    ( sK8 != X0
    | sK11 != X1
    | v1_partfun1(X1,X0) != iProver_top
    | v1_partfun1(sK11,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8458])).

cnf(c_8461,plain,
    ( sK8 != k1_xboole_0
    | sK11 != k1_xboole_0
    | v1_partfun1(sK11,sK8) = iProver_top
    | v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8459])).

cnf(c_6,plain,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7430,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8286,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7430,c_7431])).

cnf(c_8386,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8286,c_7430])).

cnf(c_8161,plain,
    ( ~ r1_tarski(X0,sK11)
    | ~ r1_tarski(sK11,X0)
    | sK11 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8162,plain,
    ( sK11 = X0
    | r1_tarski(X0,sK11) != iProver_top
    | r1_tarski(sK11,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8161])).

cnf(c_8164,plain,
    ( sK11 = k1_xboole_0
    | r1_tarski(sK11,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK11) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8162])).

cnf(c_8128,plain,
    ( r1_tarski(X0,sK11)
    | r2_hidden(sK3(X0,sK11),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8139,plain,
    ( r1_tarski(X0,sK11) = iProver_top
    | r2_hidden(sK3(X0,sK11),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8128])).

cnf(c_8141,plain,
    ( r1_tarski(k1_xboole_0,sK11) = iProver_top
    | r2_hidden(sK3(k1_xboole_0,sK11),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8139])).

cnf(c_6599,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7933,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_6599])).

cnf(c_7934,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7933])).

cnf(c_7798,plain,
    ( v1_partfun1(X0,X1)
    | ~ v1_partfun1(k6_partfun1(X2),X2)
    | X1 != X2
    | X0 != k6_partfun1(X2) ),
    inference(instantiation,[status(thm)],[c_6605])).

cnf(c_7799,plain,
    ( X0 != X1
    | X2 != k6_partfun1(X1)
    | v1_partfun1(X2,X0) = iProver_top
    | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7798])).

cnf(c_7801,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7799])).

cnf(c_115,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_34,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_50,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_52,plain,
    ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12561,c_12552,c_11280,c_9793,c_9076,c_8599,c_8461,c_8386,c_8164,c_8141,c_7934,c_7801,c_115,c_114,c_52,c_49,c_48,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:46:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 39
% 2.97/0.99  conjectures                             7
% 2.97/0.99  EPR                                     12
% 2.97/0.99  Horn                                    30
% 2.97/0.99  unary                                   12
% 2.97/0.99  binary                                  9
% 2.97/0.99  lits                                    91
% 2.97/0.99  lits eq                                 12
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 2
% 2.97/0.99  fd_pseudo_cond                          2
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f9,axiom,(
% 2.97/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f17,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f18,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.97/0.99    inference(flattening,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,conjecture,(
% 2.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f13,negated_conjecture,(
% 2.97/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.97/0.99    inference(negated_conjecture,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f21,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.97/0.99    inference(ennf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f22,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.97/0.99    inference(flattening,[],[f21])).
% 2.97/0.99  
% 2.97/0.99  fof(f50,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(sK11,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK11) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK11,X0,X1) & v1_funct_1(sK11))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f49,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK8,sK9,sK10)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK9) & r1_partfun1(sK10,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(X3,sK8,sK9) & v1_funct_1(X3)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_1(sK10))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f51,plain,(
% 2.97/0.99    (~r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK9) & r1_partfun1(sK10,sK11) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK11,sK8,sK9) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_1(sK10)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f22,f50,f49])).
% 2.97/0.99  
% 2.97/0.99  fof(f90,plain,(
% 2.97/0.99    v1_funct_2(sK11,sK8,sK9)),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f89,plain,(
% 2.97/0.99    v1_funct_1(sK11)),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f91,plain,(
% 2.97/0.99    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.97/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.97/0.99    inference(nnf_transformation,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.97/0.99    inference(rectify,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f70,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f99,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 2.97/0.99    inference(equality_resolution,[],[f70])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f19,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.97/0.99    inference(ennf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.97/0.99    inference(flattening,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.97/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.97/0.99    inference(definition_folding,[],[f20,f24,f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f84,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.97/0.99    inference(nnf_transformation,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f44,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.97/0.99    inference(rectify,[],[f43])).
% 2.97/0.99  
% 2.97/0.99  fof(f47,plain,(
% 2.97/0.99    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK7(X0,X1,X2,X7)) & v1_partfun1(sK7(X0,X1,X2,X7),X1) & sK7(X0,X1,X2,X7) = X7 & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X7))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f46,plain,(
% 2.97/0.99    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK6(X0,X1,X2,X3)) & v1_partfun1(sK6(X0,X1,X2,X3),X1) & sK6(X0,X1,X2,X3) = X4 & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK6(X0,X1,X2,X3))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK5(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK5(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f48,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK5(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK6(X0,X1,X2,X3)) & v1_partfun1(sK6(X0,X1,X2,X3),X1) & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3) & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK6(X0,X1,X2,X3))) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK7(X0,X1,X2,X7)) & v1_partfun1(sK7(X0,X1,X2,X7),X1) & sK7(X0,X1,X2,X7) = X7 & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f47,f46,f45])).
% 2.97/0.99  
% 2.97/0.99  fof(f77,plain,(
% 2.97/0.99    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f101,plain,(
% 2.97/0.99    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.97/0.99    inference(equality_resolution,[],[f77])).
% 2.97/0.99  
% 2.97/0.99  fof(f87,plain,(
% 2.97/0.99    v1_funct_1(sK10)),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f92,plain,(
% 2.97/0.99    r1_partfun1(sK10,sK11)),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f94,plain,(
% 2.97/0.99    ~r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10))),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f88,plain,(
% 2.97/0.99    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f3,axiom,(
% 2.97/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f15,plain,(
% 2.97/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f3])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f93,plain,(
% 2.97/0.99    k1_xboole_0 = sK8 | k1_xboole_0 != sK9),
% 2.97/0.99    inference(cnf_transformation,[],[f51])).
% 2.97/0.99  
% 2.97/0.99  fof(f6,axiom,(
% 2.97/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.99    inference(nnf_transformation,[],[f6])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.99    inference(flattening,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f63,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f98,plain,(
% 2.97/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.97/0.99    inference(equality_resolution,[],[f63])).
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.99    inference(nnf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.99    inference(rectify,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 2.97/0.99  
% 2.97/0.99  fof(f52,plain,(
% 2.97/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f14,plain,(
% 2.97/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(nnf_transformation,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(rectify,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f55,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f33])).
% 2.97/0.99  
% 2.97/0.99  fof(f64,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f97,plain,(
% 2.97/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.97/0.99    inference(equality_resolution,[],[f64])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,axiom,(
% 2.97/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f86,plain,(
% 2.97/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f65,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f40])).
% 2.97/0.99  
% 2.97/0.99  fof(f5,axiom,(
% 2.97/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.99    inference(nnf_transformation,[],[f5])).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.99    inference(flattening,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ? [X0] : v1_xboole_0(X0)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    v1_xboole_0(sK4)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f58,plain,(
% 2.97/0.99    v1_xboole_0(sK4)),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f85,plain,(
% 2.97/0.99    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_16,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | v1_partfun1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | v1_xboole_0(X2) ),
% 2.97/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_39,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK11,sK8,sK9) ),
% 2.97/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_497,plain,
% 2.97/0.99      ( v1_partfun1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | v1_xboole_0(X2)
% 2.97/0.99      | sK9 != X2
% 2.97/0.99      | sK8 != X1
% 2.97/0.99      | sK11 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_498,plain,
% 2.97/0.99      ( v1_partfun1(sK11,sK8)
% 2.97/0.99      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 2.97/0.99      | ~ v1_funct_1(sK11)
% 2.97/0.99      | v1_xboole_0(sK9) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_497]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_40,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK11) ),
% 2.97/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_38,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_500,plain,
% 2.97/0.99      ( v1_partfun1(sK11,sK8) | v1_xboole_0(sK9) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_498,c_40,c_38]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7404,plain,
% 2.97/0.99      ( v1_partfun1(sK11,sK8) = iProver_top
% 2.97/0.99      | v1_xboole_0(sK9) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7409,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_19,plain,
% 2.97/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_32,plain,
% 2.97/0.99      ( sP1(X0,X1,X2)
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.97/0.99      | ~ v1_funct_1(X2) ),
% 2.97/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_514,plain,
% 2.97/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.97/0.99      | ~ v1_funct_1(X3)
% 2.97/0.99      | X4 != X1
% 2.97/0.99      | X3 != X0
% 2.97/0.99      | X5 != X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_515,plain,
% 2.97/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v1_funct_1(X0) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7403,plain,
% 2.97/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
% 2.97/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,plain,
% 2.97/0.99      ( ~ sP0(X0,X1,X2,X3)
% 2.97/0.99      | ~ r1_partfun1(X0,X4)
% 2.97/0.99      | ~ v1_partfun1(X4,X1)
% 2.97/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | r2_hidden(X4,X3)
% 2.97/0.99      | ~ v1_funct_1(X4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7419,plain,
% 2.97/0.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 2.97/0.99      | r1_partfun1(X0,X4) != iProver_top
% 2.97/0.99      | v1_partfun1(X4,X1) != iProver_top
% 2.97/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.99      | r2_hidden(X4,X3) = iProver_top
% 2.97/0.99      | v1_funct_1(X4) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10647,plain,
% 2.97/0.99      ( sP0(X0,sK8,sK9,X1) != iProver_top
% 2.97/0.99      | r1_partfun1(X0,sK11) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | r2_hidden(sK11,X1) = iProver_top
% 2.97/0.99      | v1_funct_1(sK11) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7409,c_7419]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_45,plain,
% 2.97/0.99      ( v1_funct_1(sK11) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11176,plain,
% 2.97/0.99      ( r2_hidden(sK11,X1) = iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | r1_partfun1(X0,sK11) != iProver_top
% 2.97/0.99      | sP0(X0,sK8,sK9,X1) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_10647,c_45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11177,plain,
% 2.97/0.99      ( sP0(X0,sK8,sK9,X1) != iProver_top
% 2.97/0.99      | r1_partfun1(X0,sK11) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | r2_hidden(sK11,X1) = iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_11176]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11186,plain,
% 2.97/0.99      ( r1_partfun1(X0,sK11) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 2.97/0.99      | r2_hidden(sK11,k5_partfun1(sK8,sK9,X0)) = iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7403,c_11177]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11279,plain,
% 2.97/0.99      ( r1_partfun1(sK11,sK11) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | r2_hidden(sK11,k5_partfun1(sK8,sK9,sK11)) = iProver_top
% 2.97/0.99      | v1_funct_1(sK11) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7409,c_11186]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_42,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK10) ),
% 2.97/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_43,plain,
% 2.97/0.99      ( v1_funct_1(sK10) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_37,negated_conjecture,
% 2.97/0.99      ( r1_partfun1(sK10,sK11) ),
% 2.97/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_48,plain,
% 2.97/0.99      ( r1_partfun1(sK10,sK11) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_35,negated_conjecture,
% 2.97/0.99      ( ~ r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_49,plain,
% 2.97/0.99      ( r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_41,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7407,plain,
% 2.97/0.99      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11280,plain,
% 2.97/0.99      ( r1_partfun1(sK10,sK11) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) != iProver_top
% 2.97/0.99      | r2_hidden(sK11,k5_partfun1(sK8,sK9,sK10)) = iProver_top
% 2.97/0.99      | v1_funct_1(sK10) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7407,c_11186]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11439,plain,
% 2.97/0.99      ( v1_partfun1(sK11,sK8) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_11279,c_43,c_48,c_49,c_11280]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11444,plain,
% 2.97/0.99      ( v1_xboole_0(sK9) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7404,c_11439]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5,plain,
% 2.97/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7431,plain,
% 2.97/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11453,plain,
% 2.97/0.99      ( sK9 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_11444,c_7431]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12549,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))) = iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_11453,c_7409]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,negated_conjecture,
% 2.97/0.99      ( k1_xboole_0 != sK9 | k1_xboole_0 = sK8 ),
% 2.97/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12551,plain,
% 2.97/0.99      ( sK8 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_11453,c_36]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12552,plain,
% 2.97/0.99      ( sK8 = k1_xboole_0 ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_12551]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12559,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_12549,c_12552]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12561,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_12559,c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9790,plain,
% 2.97/0.99      ( ~ r2_hidden(sK3(X0,sK11),X0) | ~ v1_xboole_0(X0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9791,plain,
% 2.97/0.99      ( r2_hidden(sK3(X0,sK11),X0) != iProver_top
% 2.97/0.99      | v1_xboole_0(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_9790]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9793,plain,
% 2.97/0.99      ( r2_hidden(sK3(k1_xboole_0,sK11),k1_xboole_0) != iProver_top
% 2.97/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_9791]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7433,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7435,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.97/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8576,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7433,c_7435]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10,plain,
% 2.97/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_33,plain,
% 2.97/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7413,plain,
% 2.97/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8171,plain,
% 2.97/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_10,c_7413]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_14,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7426,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8441,plain,
% 2.97/0.99      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_8171,c_7426]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7429,plain,
% 2.97/0.99      ( X0 = X1
% 2.97/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.97/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8667,plain,
% 2.97/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_8441,c_7429]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9076,plain,
% 2.97/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_8576,c_8667]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8596,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK11,k1_zfmisc_1(X0)) | r1_tarski(sK11,X0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8597,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(X0)) != iProver_top
% 2.97/0.99      | r1_tarski(sK11,X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8596]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8599,plain,
% 2.97/0.99      ( m1_subset_1(sK11,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | r1_tarski(sK11,k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8597]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6605,plain,
% 2.97/0.99      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8458,plain,
% 2.97/0.99      ( ~ v1_partfun1(X0,X1)
% 2.97/0.99      | v1_partfun1(sK11,sK8)
% 2.97/0.99      | sK8 != X1
% 2.97/0.99      | sK11 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_6605]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8459,plain,
% 2.97/0.99      ( sK8 != X0
% 2.97/0.99      | sK11 != X1
% 2.97/0.99      | v1_partfun1(X1,X0) != iProver_top
% 2.97/0.99      | v1_partfun1(sK11,sK8) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8458]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8461,plain,
% 2.97/0.99      ( sK8 != k1_xboole_0
% 2.97/0.99      | sK11 != k1_xboole_0
% 2.97/0.99      | v1_partfun1(sK11,sK8) = iProver_top
% 2.97/0.99      | v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8459]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6,plain,
% 2.97/0.99      ( v1_xboole_0(sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7430,plain,
% 2.97/0.99      ( v1_xboole_0(sK4) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8286,plain,
% 2.97/0.99      ( sK4 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7430,c_7431]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8386,plain,
% 2.97/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_8286,c_7430]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8161,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,sK11) | ~ r1_tarski(sK11,X0) | sK11 = X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8162,plain,
% 2.97/0.99      ( sK11 = X0
% 2.97/0.99      | r1_tarski(X0,sK11) != iProver_top
% 2.97/0.99      | r1_tarski(sK11,X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8161]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8164,plain,
% 2.97/0.99      ( sK11 = k1_xboole_0
% 2.97/0.99      | r1_tarski(sK11,k1_xboole_0) != iProver_top
% 2.97/0.99      | r1_tarski(k1_xboole_0,sK11) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8162]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8128,plain,
% 2.97/0.99      ( r1_tarski(X0,sK11) | r2_hidden(sK3(X0,sK11),X0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8139,plain,
% 2.97/0.99      ( r1_tarski(X0,sK11) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,sK11),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8128]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8141,plain,
% 2.97/0.99      ( r1_tarski(k1_xboole_0,sK11) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(k1_xboole_0,sK11),k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8139]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6599,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7933,plain,
% 2.97/0.99      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_6599]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7934,plain,
% 2.97/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 2.97/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_7933]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7798,plain,
% 2.97/0.99      ( v1_partfun1(X0,X1)
% 2.97/0.99      | ~ v1_partfun1(k6_partfun1(X2),X2)
% 2.97/0.99      | X1 != X2
% 2.97/0.99      | X0 != k6_partfun1(X2) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_6605]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7799,plain,
% 2.97/0.99      ( X0 != X1
% 2.97/0.99      | X2 != k6_partfun1(X1)
% 2.97/0.99      | v1_partfun1(X2,X0) = iProver_top
% 2.97/0.99      | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_7798]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7801,plain,
% 2.97/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.97/0.99      | k1_xboole_0 != k1_xboole_0
% 2.97/0.99      | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
% 2.97/0.99      | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_7799]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_115,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12,plain,
% 2.97/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = X0
% 2.97/0.99      | k1_xboole_0 = X1 ),
% 2.97/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_114,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,plain,
% 2.97/0.99      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_50,plain,
% 2.97/0.99      ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_52,plain,
% 2.97/0.99      ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_50]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(contradiction,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(minisat,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_12561,c_12552,c_11280,c_9793,c_9076,c_8599,c_8461,
% 2.97/0.99                 c_8386,c_8164,c_8141,c_7934,c_7801,c_115,c_114,c_52,
% 2.97/0.99                 c_49,c_48,c_43]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.011
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.011
% 2.97/0.99  total_time:                             0.294
% 2.97/0.99  num_of_symbols:                         56
% 2.97/0.99  num_of_terms:                           6741
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          0
% 2.97/0.99  num_of_split_atoms:                     0
% 2.97/0.99  num_of_reused_defs:                     0
% 2.97/0.99  num_eq_ax_congr_red:                    67
% 2.97/0.99  num_of_sem_filtered_clauses:            1
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       183
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        195
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        8
% 2.97/0.99  pred_elim:                              2
% 2.97/0.99  pred_elim_cl:                           2
% 2.97/0.99  pred_elim_cycles:                       14
% 2.97/0.99  merged_defs:                            8
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          9
% 2.97/0.99  prep_cycles:                            4
% 2.97/0.99  pred_elim_time:                         0.09
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                39
% 2.97/0.99  conjectures:                            7
% 2.97/0.99  epr:                                    12
% 2.97/0.99  horn:                                   30
% 2.97/0.99  ground:                                 9
% 2.97/0.99  unary:                                  12
% 2.97/0.99  binary:                                 9
% 2.97/0.99  lits:                                   91
% 2.97/0.99  lits_eq:                                12
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                2
% 2.97/0.99  fd_pseudo_cond:                         2
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      28
% 2.97/0.99  prop_fast_solver_calls:                 2491
% 2.97/0.99  smt_solver_calls:                       0
% 2.97/0.99  smt_fast_solver_calls:                  0
% 2.97/0.99  prop_num_of_clauses:                    2624
% 2.97/0.99  prop_preprocess_simplified:             9003
% 2.97/0.99  prop_fo_subsumed:                       45
% 2.97/0.99  prop_solver_time:                       0.
% 2.97/0.99  smt_solver_time:                        0.
% 2.97/0.99  smt_fast_solver_time:                   0.
% 2.97/0.99  prop_fast_solver_time:                  0.
% 2.97/0.99  prop_unsat_core_time:                   0.
% 2.97/0.99  
% 2.97/0.99  ------ QBF
% 2.97/0.99  
% 2.97/0.99  qbf_q_res:                              0
% 2.97/0.99  qbf_num_tautologies:                    0
% 2.97/0.99  qbf_prep_cycles:                        0
% 2.97/0.99  
% 2.97/0.99  ------ BMC1
% 2.97/0.99  
% 2.97/0.99  bmc1_current_bound:                     -1
% 2.97/0.99  bmc1_last_solved_bound:                 -1
% 2.97/0.99  bmc1_unsat_core_size:                   -1
% 2.97/0.99  bmc1_unsat_core_parents_size:           -1
% 2.97/0.99  bmc1_merge_next_fun:                    0
% 2.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation
% 2.97/0.99  
% 2.97/0.99  inst_num_of_clauses:                    627
% 2.97/0.99  inst_num_in_passive:                    85
% 2.97/0.99  inst_num_in_active:                     343
% 2.97/0.99  inst_num_in_unprocessed:                199
% 2.97/0.99  inst_num_of_loops:                      480
% 2.97/0.99  inst_num_of_learning_restarts:          0
% 2.97/0.99  inst_num_moves_active_passive:          134
% 2.97/0.99  inst_lit_activity:                      0
% 2.97/0.99  inst_lit_activity_moves:                0
% 2.97/0.99  inst_num_tautologies:                   0
% 2.97/0.99  inst_num_prop_implied:                  0
% 2.97/0.99  inst_num_existing_simplified:           0
% 2.97/0.99  inst_num_eq_res_simplified:             0
% 2.97/0.99  inst_num_child_elim:                    0
% 2.97/0.99  inst_num_of_dismatching_blockings:      132
% 2.97/0.99  inst_num_of_non_proper_insts:           623
% 2.97/0.99  inst_num_of_duplicates:                 0
% 2.97/0.99  inst_inst_num_from_inst_to_res:         0
% 2.97/0.99  inst_dismatching_checking_time:         0.
% 2.97/0.99  
% 2.97/0.99  ------ Resolution
% 2.97/0.99  
% 2.97/0.99  res_num_of_clauses:                     0
% 2.97/0.99  res_num_in_passive:                     0
% 2.97/0.99  res_num_in_active:                      0
% 2.97/0.99  res_num_of_loops:                       187
% 2.97/0.99  res_forward_subset_subsumed:            46
% 2.97/0.99  res_backward_subset_subsumed:           0
% 2.97/0.99  res_forward_subsumed:                   0
% 2.97/0.99  res_backward_subsumed:                  0
% 2.97/0.99  res_forward_subsumption_resolution:     6
% 2.97/0.99  res_backward_subsumption_resolution:    0
% 2.97/0.99  res_clause_to_clause_subsumption:       579
% 2.97/0.99  res_orphan_elimination:                 0
% 2.97/0.99  res_tautology_del:                      79
% 2.97/0.99  res_num_eq_res_simplified:              0
% 2.97/0.99  res_num_sel_changes:                    0
% 2.97/0.99  res_moves_from_active_to_pass:          0
% 2.97/0.99  
% 2.97/0.99  ------ Superposition
% 2.97/0.99  
% 2.97/0.99  sup_time_total:                         0.
% 2.97/0.99  sup_time_generating:                    0.
% 2.97/0.99  sup_time_sim_full:                      0.
% 2.97/0.99  sup_time_sim_immed:                     0.
% 2.97/0.99  
% 2.97/0.99  sup_num_of_clauses:                     119
% 2.97/0.99  sup_num_in_active:                      60
% 2.97/0.99  sup_num_in_passive:                     59
% 2.97/0.99  sup_num_of_loops:                       94
% 2.97/0.99  sup_fw_superposition:                   93
% 2.97/0.99  sup_bw_superposition:                   59
% 2.97/0.99  sup_immediate_simplified:               49
% 2.97/0.99  sup_given_eliminated:                   1
% 2.97/0.99  comparisons_done:                       0
% 2.97/0.99  comparisons_avoided:                    0
% 2.97/0.99  
% 2.97/0.99  ------ Simplifications
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  sim_fw_subset_subsumed:                 3
% 2.97/0.99  sim_bw_subset_subsumed:                 1
% 2.97/0.99  sim_fw_subsumed:                        7
% 2.97/0.99  sim_bw_subsumed:                        0
% 2.97/0.99  sim_fw_subsumption_res:                 0
% 2.97/0.99  sim_bw_subsumption_res:                 0
% 2.97/0.99  sim_tautology_del:                      4
% 2.97/0.99  sim_eq_tautology_del:                   13
% 2.97/0.99  sim_eq_res_simp:                        1
% 2.97/0.99  sim_fw_demodulated:                     21
% 2.97/0.99  sim_bw_demodulated:                     34
% 2.97/0.99  sim_light_normalised:                   33
% 2.97/0.99  sim_joinable_taut:                      0
% 2.97/0.99  sim_joinable_simp:                      0
% 2.97/0.99  sim_ac_normalised:                      0
% 2.97/0.99  sim_smt_subsumption:                    0
% 2.97/0.99  
%------------------------------------------------------------------------------
