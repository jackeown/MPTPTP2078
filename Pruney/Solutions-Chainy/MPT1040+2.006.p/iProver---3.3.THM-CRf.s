%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:45 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 736 expanded)
%              Number of clauses        :   91 ( 229 expanded)
%              Number of leaves         :   20 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          :  579 (5328 expanded)
%              Number of equality atoms :  201 (1293 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(sK9,k5_partfun1(X0,X1,X2))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK9,X0,X1)
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
          ( ~ r2_hidden(X3,k5_partfun1(sK6,sK7,sK8))
          & ( k1_xboole_0 = sK6
            | k1_xboole_0 != sK7 )
          & r1_partfun1(sK8,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_2(X3,sK6,sK7)
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK7 )
    & r1_partfun1(sK8,sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f17,f34,f33])).

fof(f64,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,plain,(
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

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f51,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f51])).

fof(f61,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    r1_partfun1(sK8,sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f15,f19,f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2,f21])).

fof(f37,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_316,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK7 != X2
    | sK6 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_317,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_319,plain,
    ( v1_partfun1(sK9,sK6)
    | v1_xboole_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_30,c_28])).

cnf(c_8266,plain,
    ( v1_partfun1(sK9,sK6) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_8270,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r2_hidden(X4,X3)
    | ~ r1_partfun1(X0,X4)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8280,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10502,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8270,c_8280])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_33,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_37,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( r1_partfun1(sK8,sK9) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( r1_partfun1(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_333,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X2 != X5
    | X1 != X4
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_9])).

cnf(c_334,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_8560,plain,
    ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_8671,plain,
    ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_8560])).

cnf(c_8672,plain,
    ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8671])).

cnf(c_8573,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r2_hidden(sK9,X3)
    | ~ r1_partfun1(X0,sK9)
    | ~ v1_partfun1(sK9,X1)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_8786,plain,
    ( ~ sP0(sK8,X0,X1,X2)
    | r2_hidden(sK9,X2)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_8573])).

cnf(c_9017,plain,
    ( ~ sP0(sK8,sK6,X0,X1)
    | r2_hidden(sK9,X1)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_8786])).

cnf(c_9305,plain,
    ( ~ sP0(sK8,sK6,sK7,X0)
    | r2_hidden(sK9,X0)
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_9017])).

cnf(c_9812,plain,
    ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
    | ~ r1_partfun1(sK8,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_9305])).

cnf(c_9813,plain,
    ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) = iProver_top
    | r1_partfun1(sK8,sK9) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9812])).

cnf(c_10843,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10502,c_33,c_34,c_35,c_37,c_38,c_39,c_8672,c_9813])).

cnf(c_10848,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8266,c_10843])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8289,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10926,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10848,c_8289])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12024,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10926,c_26])).

cnf(c_12025,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12024])).

cnf(c_12157,plain,
    ( v1_partfun1(sK9,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12025,c_10843])).

cnf(c_12022,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10926,c_8270])).

cnf(c_12032,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12022,c_12025])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12034,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12032,c_3])).

cnf(c_7787,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9909,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(sK9,X2)
    | X2 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_7787])).

cnf(c_9910,plain,
    ( X0 != X1
    | sK9 != X2
    | v1_partfun1(X2,X1) != iProver_top
    | v1_partfun1(sK9,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9909])).

cnf(c_9912,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_partfun1(sK9,k1_xboole_0) = iProver_top
    | v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9910])).

cnf(c_7782,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8894,plain,
    ( X0 != X1
    | sK9 != X1
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_7782])).

cnf(c_9702,plain,
    ( X0 != sK9
    | sK9 = X0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_8894])).

cnf(c_9703,plain,
    ( sK9 != sK9
    | sK9 = k1_xboole_0
    | k1_xboole_0 != sK9 ),
    inference(instantiation,[status(thm)],[c_9702])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9088,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9090,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9088])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8274,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8998,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_8274])).

cnf(c_9009,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8998])).

cnf(c_8970,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8974,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8970])).

cnf(c_8912,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8913,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8912])).

cnf(c_8915,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK9) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8913])).

cnf(c_8677,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7781,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8614,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_7781])).

cnf(c_8588,plain,
    ( ~ v1_xboole_0(sK9)
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8591,plain,
    ( k1_xboole_0 = sK9
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8588])).

cnf(c_8552,plain,
    ( v1_partfun1(X0,X1)
    | ~ v1_partfun1(k6_partfun1(X2),X2)
    | X1 != X2
    | X0 != k6_partfun1(X2) ),
    inference(instantiation,[status(thm)],[c_7787])).

cnf(c_8553,plain,
    ( X0 != X1
    | X2 != k6_partfun1(X1)
    | v1_partfun1(X2,X0) = iProver_top
    | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8552])).

cnf(c_8555,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8553])).

cnf(c_7783,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_8542,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_7783])).

cnf(c_8543,plain,
    ( X0 != sK2
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8542])).

cnf(c_8545,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8543])).

cnf(c_8544,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_8542])).

cnf(c_1,plain,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_98,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_97,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_24,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_40,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_42,plain,
    ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12157,c_12034,c_9912,c_9703,c_9090,c_9009,c_8974,c_8915,c_8677,c_8614,c_8591,c_8555,c_8545,c_8544,c_98,c_1,c_97,c_96,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:51:17 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.98  
% 2.70/0.98  ------  iProver source info
% 2.70/0.98  
% 2.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.98  git: non_committed_changes: false
% 2.70/0.98  git: last_make_outside_of_git: false
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     num_symb
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       true
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.98  --res_prop_simpl_new                    false
% 2.70/0.98  --res_prop_simpl_given                  true
% 2.70/0.98  --res_passive_queue_type                priority_queues
% 2.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.98  --res_passive_queues_freq               [15;5]
% 2.70/0.98  --res_forward_subs                      full
% 2.70/0.98  --res_backward_subs                     full
% 2.70/0.98  --res_forward_subs_resolution           true
% 2.70/0.98  --res_backward_subs_resolution          true
% 2.70/0.98  --res_orphan_elimination                true
% 2.70/0.98  --res_time_limit                        2.
% 2.70/0.98  --res_out_proof                         true
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Options
% 2.70/0.98  
% 2.70/0.98  --superposition_flag                    true
% 2.70/0.98  --sup_passive_queue_type                priority_queues
% 2.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.98  --demod_completeness_check              fast
% 2.70/0.98  --demod_use_ground                      true
% 2.70/0.98  --sup_to_prop_solver                    passive
% 2.70/0.98  --sup_prop_simpl_new                    true
% 2.70/0.98  --sup_prop_simpl_given                  true
% 2.70/0.98  --sup_fun_splitting                     false
% 2.70/0.98  --sup_smt_interval                      50000
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Simplification Setup
% 2.70/0.98  
% 2.70/0.98  --sup_indices_passive                   []
% 2.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_full_bw                           [BwDemod]
% 2.70/0.98  --sup_immed_triv                        [TrivRules]
% 2.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_immed_bw_main                     []
% 2.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  
% 2.70/0.98  ------ Combination Options
% 2.70/0.98  
% 2.70/0.98  --comb_res_mult                         3
% 2.70/0.98  --comb_sup_mult                         2
% 2.70/0.98  --comb_inst_mult                        10
% 2.70/0.98  
% 2.70/0.98  ------ Debug Options
% 2.70/0.98  
% 2.70/0.98  --dbg_backtrace                         false
% 2.70/0.98  --dbg_dump_prop_clauses                 false
% 2.70/0.98  --dbg_dump_prop_clauses_file            -
% 2.70/0.98  --dbg_out_stat                          false
% 2.70/0.98  ------ Parsing...
% 2.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.98  ------ Proving...
% 2.70/0.98  ------ Problem Properties 
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  clauses                                 30
% 2.70/0.98  conjectures                             7
% 2.70/0.98  EPR                                     7
% 2.70/0.98  Horn                                    23
% 2.70/0.98  unary                                   11
% 2.70/0.98  binary                                  3
% 2.70/0.98  lits                                    72
% 2.70/0.98  lits eq                                 11
% 2.70/0.98  fd_pure                                 0
% 2.70/0.98  fd_pseudo                               0
% 2.70/0.98  fd_cond                                 2
% 2.70/0.98  fd_pseudo_cond                          1
% 2.70/0.98  AC symbols                              0
% 2.70/0.98  
% 2.70/0.98  ------ Schedule dynamic 5 is on 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  Current options:
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     none
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       false
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.98  --res_prop_simpl_new                    false
% 2.70/0.98  --res_prop_simpl_given                  true
% 2.70/0.98  --res_passive_queue_type                priority_queues
% 2.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.98  --res_passive_queues_freq               [15;5]
% 2.70/0.98  --res_forward_subs                      full
% 2.70/0.98  --res_backward_subs                     full
% 2.70/0.98  --res_forward_subs_resolution           true
% 2.70/0.98  --res_backward_subs_resolution          true
% 2.70/0.98  --res_orphan_elimination                true
% 2.70/0.98  --res_time_limit                        2.
% 2.70/0.98  --res_out_proof                         true
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Options
% 2.70/0.98  
% 2.70/0.98  --superposition_flag                    true
% 2.70/0.98  --sup_passive_queue_type                priority_queues
% 2.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.98  --demod_completeness_check              fast
% 2.70/0.98  --demod_use_ground                      true
% 2.70/0.98  --sup_to_prop_solver                    passive
% 2.70/0.98  --sup_prop_simpl_new                    true
% 2.70/0.98  --sup_prop_simpl_given                  true
% 2.70/0.98  --sup_fun_splitting                     false
% 2.70/0.98  --sup_smt_interval                      50000
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Simplification Setup
% 2.70/0.98  
% 2.70/0.98  --sup_indices_passive                   []
% 2.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_full_bw                           [BwDemod]
% 2.70/0.98  --sup_immed_triv                        [TrivRules]
% 2.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_immed_bw_main                     []
% 2.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  
% 2.70/0.98  ------ Combination Options
% 2.70/0.98  
% 2.70/0.98  --comb_res_mult                         3
% 2.70/0.98  --comb_sup_mult                         2
% 2.70/0.98  --comb_inst_mult                        10
% 2.70/0.98  
% 2.70/0.98  ------ Debug Options
% 2.70/0.98  
% 2.70/0.98  --dbg_backtrace                         false
% 2.70/0.98  --dbg_dump_prop_clauses                 false
% 2.70/0.98  --dbg_dump_prop_clauses_file            -
% 2.70/0.98  --dbg_out_stat                          false
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  ------ Proving...
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  % SZS status Theorem for theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  fof(f5,axiom,(
% 2.70/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f12,plain,(
% 2.70/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.70/0.98    inference(ennf_transformation,[],[f5])).
% 2.70/0.98  
% 2.70/0.98  fof(f13,plain,(
% 2.70/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.70/0.98    inference(flattening,[],[f12])).
% 2.70/0.98  
% 2.70/0.98  fof(f43,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f13])).
% 2.70/0.98  
% 2.70/0.98  fof(f8,conjecture,(
% 2.70/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f9,negated_conjecture,(
% 2.70/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.70/0.98    inference(negated_conjecture,[],[f8])).
% 2.70/0.98  
% 2.70/0.98  fof(f16,plain,(
% 2.70/0.98    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.70/0.98    inference(ennf_transformation,[],[f9])).
% 2.70/0.98  
% 2.70/0.98  fof(f17,plain,(
% 2.70/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.70/0.98    inference(flattening,[],[f16])).
% 2.70/0.98  
% 2.70/0.98  fof(f34,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(sK9,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK9) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK9,X0,X1) & v1_funct_1(sK9))) )),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f33,plain,(
% 2.70/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK6,sK7,sK8)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK7) & r1_partfun1(sK8,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(X3,sK6,sK7) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8))),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f35,plain,(
% 2.70/0.98    (~r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK7) & r1_partfun1(sK8,sK9) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8)),
% 2.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f17,f34,f33])).
% 2.70/0.98  
% 2.70/0.98  fof(f64,plain,(
% 2.70/0.98    v1_funct_2(sK9,sK6,sK7)),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f63,plain,(
% 2.70/0.98    v1_funct_1(sK9)),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f65,plain,(
% 2.70/0.98    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f18,plain,(
% 2.70/0.98    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.70/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.70/0.98  
% 2.70/0.98  fof(f27,plain,(
% 2.70/0.98    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.70/0.98    inference(nnf_transformation,[],[f18])).
% 2.70/0.98  
% 2.70/0.98  fof(f28,plain,(
% 2.70/0.98    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.70/0.98    inference(rectify,[],[f27])).
% 2.70/0.98  
% 2.70/0.98  fof(f31,plain,(
% 2.70/0.98    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f30,plain,(
% 2.70/0.98    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f29,plain,(
% 2.70/0.98    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f32,plain,(
% 2.70/0.98    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 2.70/0.98  
% 2.70/0.98  fof(f51,plain,(
% 2.70/0.98    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f32])).
% 2.70/0.98  
% 2.70/0.98  fof(f73,plain,(
% 2.70/0.98    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.70/0.98    inference(equality_resolution,[],[f51])).
% 2.70/0.98  
% 2.70/0.98  fof(f61,plain,(
% 2.70/0.98    v1_funct_1(sK8)),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f62,plain,(
% 2.70/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f66,plain,(
% 2.70/0.98    r1_partfun1(sK8,sK9)),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f68,plain,(
% 2.70/0.98    ~r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f6,axiom,(
% 2.70/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f14,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.70/0.98    inference(ennf_transformation,[],[f6])).
% 2.70/0.98  
% 2.70/0.98  fof(f15,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.70/0.98    inference(flattening,[],[f14])).
% 2.70/0.98  
% 2.70/0.98  fof(f19,plain,(
% 2.70/0.98    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.70/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.70/0.98  
% 2.70/0.98  fof(f20,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.70/0.98    inference(definition_folding,[],[f15,f19,f18])).
% 2.70/0.98  
% 2.70/0.98  fof(f58,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f20])).
% 2.70/0.98  
% 2.70/0.98  fof(f25,plain,(
% 2.70/0.98    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.70/0.98    inference(nnf_transformation,[],[f19])).
% 2.70/0.98  
% 2.70/0.98  fof(f26,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.70/0.98    inference(rectify,[],[f25])).
% 2.70/0.98  
% 2.70/0.98  fof(f44,plain,(
% 2.70/0.98    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f26])).
% 2.70/0.98  
% 2.70/0.98  fof(f71,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 2.70/0.98    inference(equality_resolution,[],[f44])).
% 2.70/0.98  
% 2.70/0.98  fof(f1,axiom,(
% 2.70/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f10,plain,(
% 2.70/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.70/0.98    inference(ennf_transformation,[],[f1])).
% 2.70/0.98  
% 2.70/0.98  fof(f36,plain,(
% 2.70/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f10])).
% 2.70/0.98  
% 2.70/0.98  fof(f67,plain,(
% 2.70/0.98    k1_xboole_0 = sK6 | k1_xboole_0 != sK7),
% 2.70/0.98    inference(cnf_transformation,[],[f35])).
% 2.70/0.98  
% 2.70/0.98  fof(f3,axiom,(
% 2.70/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f23,plain,(
% 2.70/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.70/0.98    inference(nnf_transformation,[],[f3])).
% 2.70/0.98  
% 2.70/0.98  fof(f24,plain,(
% 2.70/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.70/0.98    inference(flattening,[],[f23])).
% 2.70/0.98  
% 2.70/0.98  fof(f39,plain,(
% 2.70/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.70/0.98    inference(cnf_transformation,[],[f24])).
% 2.70/0.98  
% 2.70/0.98  fof(f70,plain,(
% 2.70/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.70/0.98    inference(equality_resolution,[],[f39])).
% 2.70/0.98  
% 2.70/0.98  fof(f4,axiom,(
% 2.70/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f11,plain,(
% 2.70/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.70/0.98    inference(ennf_transformation,[],[f4])).
% 2.70/0.98  
% 2.70/0.98  fof(f41,plain,(
% 2.70/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f11])).
% 2.70/0.98  
% 2.70/0.98  fof(f40,plain,(
% 2.70/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.70/0.98    inference(cnf_transformation,[],[f24])).
% 2.70/0.98  
% 2.70/0.98  fof(f69,plain,(
% 2.70/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.70/0.98    inference(equality_resolution,[],[f40])).
% 2.70/0.98  
% 2.70/0.98  fof(f7,axiom,(
% 2.70/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f60,plain,(
% 2.70/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.70/0.98    inference(cnf_transformation,[],[f7])).
% 2.70/0.98  
% 2.70/0.98  fof(f2,axiom,(
% 2.70/0.98    ? [X0] : v1_xboole_0(X0)),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f21,plain,(
% 2.70/0.98    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK2)),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f22,plain,(
% 2.70/0.98    v1_xboole_0(sK2)),
% 2.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2,f21])).
% 2.70/0.98  
% 2.70/0.98  fof(f37,plain,(
% 2.70/0.98    v1_xboole_0(sK2)),
% 2.70/0.98    inference(cnf_transformation,[],[f22])).
% 2.70/0.98  
% 2.70/0.98  fof(f38,plain,(
% 2.70/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f24])).
% 2.70/0.98  
% 2.70/0.98  fof(f59,plain,(
% 2.70/0.98    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 2.70/0.98    inference(cnf_transformation,[],[f7])).
% 2.70/0.98  
% 2.70/0.98  cnf(c_6,plain,
% 2.70/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.98      | v1_partfun1(X0,X1)
% 2.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.98      | ~ v1_funct_1(X0)
% 2.70/0.98      | v1_xboole_0(X2) ),
% 2.70/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_29,negated_conjecture,
% 2.70/0.98      ( v1_funct_2(sK9,sK6,sK7) ),
% 2.70/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_316,plain,
% 2.70/0.98      ( v1_partfun1(X0,X1)
% 2.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.98      | ~ v1_funct_1(X0)
% 2.70/0.98      | v1_xboole_0(X2)
% 2.70/0.98      | sK7 != X2
% 2.70/0.98      | sK6 != X1
% 2.70/0.98      | sK9 != X0 ),
% 2.70/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_317,plain,
% 2.70/0.98      ( v1_partfun1(sK9,sK6)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.70/0.98      | ~ v1_funct_1(sK9)
% 2.70/0.98      | v1_xboole_0(sK7) ),
% 2.70/0.98      inference(unflattening,[status(thm)],[c_316]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_30,negated_conjecture,
% 2.70/0.98      ( v1_funct_1(sK9) ),
% 2.70/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_28,negated_conjecture,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 2.70/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_319,plain,
% 2.70/0.98      ( v1_partfun1(sK9,sK6) | v1_xboole_0(sK7) ),
% 2.70/0.98      inference(global_propositional_subsumption,
% 2.70/0.98                [status(thm)],
% 2.70/0.98                [c_317,c_30,c_28]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8266,plain,
% 2.70/0.98      ( v1_partfun1(sK9,sK6) = iProver_top
% 2.70/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8270,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_16,plain,
% 2.70/0.98      ( ~ sP0(X0,X1,X2,X3)
% 2.70/0.98      | r2_hidden(X4,X3)
% 2.70/0.98      | ~ r1_partfun1(X0,X4)
% 2.70/0.98      | ~ v1_partfun1(X4,X1)
% 2.70/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.98      | ~ v1_funct_1(X4) ),
% 2.70/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8280,plain,
% 2.70/0.98      ( sP0(X0,X1,X2,X3) != iProver_top
% 2.70/0.98      | r2_hidden(X4,X3) = iProver_top
% 2.70/0.98      | r1_partfun1(X0,X4) != iProver_top
% 2.70/0.98      | v1_partfun1(X4,X1) != iProver_top
% 2.70/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.70/0.98      | v1_funct_1(X4) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_10502,plain,
% 2.70/0.98      ( sP0(X0,sK6,sK7,X1) != iProver_top
% 2.70/0.98      | r2_hidden(sK9,X1) = iProver_top
% 2.70/0.98      | r1_partfun1(X0,sK9) != iProver_top
% 2.70/0.98      | v1_partfun1(sK9,sK6) != iProver_top
% 2.70/0.98      | v1_funct_1(sK9) != iProver_top ),
% 2.70/0.98      inference(superposition,[status(thm)],[c_8270,c_8280]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_32,negated_conjecture,
% 2.70/0.98      ( v1_funct_1(sK8) ),
% 2.70/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_33,plain,
% 2.70/0.98      ( v1_funct_1(sK8) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_31,negated_conjecture,
% 2.70/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 2.70/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_34,plain,
% 2.70/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_35,plain,
% 2.70/0.98      ( v1_funct_1(sK9) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_37,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_27,negated_conjecture,
% 2.70/0.98      ( r1_partfun1(sK8,sK9) ),
% 2.70/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_38,plain,
% 2.70/0.98      ( r1_partfun1(sK8,sK9) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_25,negated_conjecture,
% 2.70/0.98      ( ~ r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) ),
% 2.70/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_39,plain,
% 2.70/0.98      ( r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_22,plain,
% 2.70/0.98      ( sP1(X0,X1,X2)
% 2.70/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.70/0.98      | ~ v1_funct_1(X2) ),
% 2.70/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9,plain,
% 2.70/0.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 2.70/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_333,plain,
% 2.70/0.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.70/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.70/0.98      | ~ v1_funct_1(X3)
% 2.70/0.98      | X2 != X5
% 2.70/0.98      | X1 != X4
% 2.70/0.98      | X0 != X3 ),
% 2.70/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_9]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_334,plain,
% 2.70/0.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.98      | ~ v1_funct_1(X0) ),
% 2.70/0.98      inference(unflattening,[status(thm)],[c_333]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8560,plain,
% 2.70/0.98      ( sP0(sK8,X0,X1,k5_partfun1(X0,X1,sK8))
% 2.70/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.98      | ~ v1_funct_1(sK8) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_334]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8671,plain,
% 2.70/0.98      ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 2.70/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.70/0.98      | ~ v1_funct_1(sK8) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8560]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8672,plain,
% 2.70/0.98      ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8)) = iProver_top
% 2.70/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 2.70/0.98      | v1_funct_1(sK8) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8671]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8573,plain,
% 2.70/0.98      ( ~ sP0(X0,X1,X2,X3)
% 2.70/0.98      | r2_hidden(sK9,X3)
% 2.70/0.98      | ~ r1_partfun1(X0,sK9)
% 2.70/0.98      | ~ v1_partfun1(sK9,X1)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.98      | ~ v1_funct_1(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8786,plain,
% 2.70/0.98      ( ~ sP0(sK8,X0,X1,X2)
% 2.70/0.98      | r2_hidden(sK9,X2)
% 2.70/0.98      | ~ r1_partfun1(sK8,sK9)
% 2.70/0.98      | ~ v1_partfun1(sK9,X0)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.98      | ~ v1_funct_1(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8573]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9017,plain,
% 2.70/0.98      ( ~ sP0(sK8,sK6,X0,X1)
% 2.70/0.98      | r2_hidden(sK9,X1)
% 2.70/0.98      | ~ r1_partfun1(sK8,sK9)
% 2.70/0.98      | ~ v1_partfun1(sK9,sK6)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
% 2.70/0.98      | ~ v1_funct_1(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8786]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9305,plain,
% 2.70/0.98      ( ~ sP0(sK8,sK6,sK7,X0)
% 2.70/0.98      | r2_hidden(sK9,X0)
% 2.70/0.98      | ~ r1_partfun1(sK8,sK9)
% 2.70/0.98      | ~ v1_partfun1(sK9,sK6)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.70/0.98      | ~ v1_funct_1(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_9017]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9812,plain,
% 2.70/0.98      ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 2.70/0.98      | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8))
% 2.70/0.98      | ~ r1_partfun1(sK8,sK9)
% 2.70/0.98      | ~ v1_partfun1(sK9,sK6)
% 2.70/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 2.70/0.98      | ~ v1_funct_1(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_9305]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9813,plain,
% 2.70/0.98      ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 2.70/0.98      | r2_hidden(sK9,k5_partfun1(sK6,sK7,sK8)) = iProver_top
% 2.70/0.98      | r1_partfun1(sK8,sK9) != iProver_top
% 2.70/0.98      | v1_partfun1(sK9,sK6) != iProver_top
% 2.70/0.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 2.70/0.98      | v1_funct_1(sK9) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_9812]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_10843,plain,
% 2.70/0.98      ( v1_partfun1(sK9,sK6) != iProver_top ),
% 2.70/0.98      inference(global_propositional_subsumption,
% 2.70/0.98                [status(thm)],
% 2.70/0.98                [c_10502,c_33,c_34,c_35,c_37,c_38,c_39,c_8672,c_9813]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_10848,plain,
% 2.70/0.98      ( v1_xboole_0(sK7) = iProver_top ),
% 2.70/0.98      inference(superposition,[status(thm)],[c_8266,c_10843]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_0,plain,
% 2.70/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.70/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8289,plain,
% 2.70/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_10926,plain,
% 2.70/0.98      ( sK7 = k1_xboole_0 ),
% 2.70/0.98      inference(superposition,[status(thm)],[c_10848,c_8289]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_26,negated_conjecture,
% 2.70/0.98      ( k1_xboole_0 != sK7 | k1_xboole_0 = sK6 ),
% 2.70/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12024,plain,
% 2.70/0.98      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.70/0.98      inference(demodulation,[status(thm)],[c_10926,c_26]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12025,plain,
% 2.70/0.98      ( sK6 = k1_xboole_0 ),
% 2.70/0.98      inference(equality_resolution_simp,[status(thm)],[c_12024]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12157,plain,
% 2.70/0.98      ( v1_partfun1(sK9,k1_xboole_0) != iProver_top ),
% 2.70/0.98      inference(demodulation,[status(thm)],[c_12025,c_10843]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12022,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 2.70/0.98      inference(demodulation,[status(thm)],[c_10926,c_8270]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12032,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.70/0.98      inference(light_normalisation,[status(thm)],[c_12022,c_12025]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_3,plain,
% 2.70/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.70/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_12034,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.70/0.98      inference(demodulation,[status(thm)],[c_12032,c_3]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_7787,plain,
% 2.70/0.98      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/0.98      theory(equality) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9909,plain,
% 2.70/0.98      ( ~ v1_partfun1(X0,X1)
% 2.70/0.98      | v1_partfun1(sK9,X2)
% 2.70/0.98      | X2 != X1
% 2.70/0.98      | sK9 != X0 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_7787]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9910,plain,
% 2.70/0.98      ( X0 != X1
% 2.70/0.98      | sK9 != X2
% 2.70/0.98      | v1_partfun1(X2,X1) != iProver_top
% 2.70/0.98      | v1_partfun1(sK9,X0) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_9909]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9912,plain,
% 2.70/0.98      ( sK9 != k1_xboole_0
% 2.70/0.98      | k1_xboole_0 != k1_xboole_0
% 2.70/0.98      | v1_partfun1(sK9,k1_xboole_0) = iProver_top
% 2.70/0.98      | v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_9910]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_7782,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8894,plain,
% 2.70/0.98      ( X0 != X1 | sK9 != X1 | sK9 = X0 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_7782]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9702,plain,
% 2.70/0.98      ( X0 != sK9 | sK9 = X0 | sK9 != sK9 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8894]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9703,plain,
% 2.70/0.98      ( sK9 != sK9 | sK9 = k1_xboole_0 | k1_xboole_0 != sK9 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_9702]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_5,plain,
% 2.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/0.98      | ~ v1_xboole_0(X1)
% 2.70/0.98      | v1_xboole_0(X0) ),
% 2.70/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9088,plain,
% 2.70/0.98      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
% 2.70/0.98      | ~ v1_xboole_0(X1)
% 2.70/0.98      | v1_xboole_0(k6_partfun1(X0)) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9090,plain,
% 2.70/0.98      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 2.70/0.98      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.70/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_9088]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_2,plain,
% 2.70/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.70/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_23,plain,
% 2.70/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.70/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8274,plain,
% 2.70/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8998,plain,
% 2.70/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.70/0.98      inference(superposition,[status(thm)],[c_2,c_8274]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_9009,plain,
% 2.70/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
% 2.70/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_8998]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8970,plain,
% 2.70/0.98      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8974,plain,
% 2.70/0.98      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.70/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8970]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8912,plain,
% 2.70/0.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
% 2.70/0.98      | ~ v1_xboole_0(X0)
% 2.70/0.98      | v1_xboole_0(sK9) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8913,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
% 2.70/0.98      | v1_xboole_0(X0) != iProver_top
% 2.70/0.98      | v1_xboole_0(sK9) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8912]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8915,plain,
% 2.70/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.70/0.98      | v1_xboole_0(sK9) = iProver_top
% 2.70/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8913]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8677,plain,
% 2.70/0.98      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_7781,plain,( X0 = X0 ),theory(equality) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8614,plain,
% 2.70/0.98      ( sK9 = sK9 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_7781]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8588,plain,
% 2.70/0.98      ( ~ v1_xboole_0(sK9) | k1_xboole_0 = sK9 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8591,plain,
% 2.70/0.98      ( k1_xboole_0 = sK9 | v1_xboole_0(sK9) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8588]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8552,plain,
% 2.70/0.98      ( v1_partfun1(X0,X1)
% 2.70/0.98      | ~ v1_partfun1(k6_partfun1(X2),X2)
% 2.70/0.98      | X1 != X2
% 2.70/0.98      | X0 != k6_partfun1(X2) ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_7787]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8553,plain,
% 2.70/0.98      ( X0 != X1
% 2.70/0.98      | X2 != k6_partfun1(X1)
% 2.70/0.98      | v1_partfun1(X2,X0) = iProver_top
% 2.70/0.98      | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8552]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8555,plain,
% 2.70/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.70/0.98      | k1_xboole_0 != k1_xboole_0
% 2.70/0.98      | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
% 2.70/0.98      | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8553]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_7783,plain,
% 2.70/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.70/0.98      theory(equality) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8542,plain,
% 2.70/0.98      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | X0 != sK2 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_7783]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8543,plain,
% 2.70/0.98      ( X0 != sK2
% 2.70/0.98      | v1_xboole_0(X0) = iProver_top
% 2.70/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8542]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8545,plain,
% 2.70/0.98      ( k1_xboole_0 != sK2
% 2.70/0.98      | v1_xboole_0(sK2) != iProver_top
% 2.70/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8543]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_8544,plain,
% 2.70/0.98      ( ~ v1_xboole_0(sK2)
% 2.70/0.98      | v1_xboole_0(k1_xboole_0)
% 2.70/0.98      | k1_xboole_0 != sK2 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_8542]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_1,plain,
% 2.70/0.98      ( v1_xboole_0(sK2) ),
% 2.70/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_98,plain,
% 2.70/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_97,plain,
% 2.70/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_4,plain,
% 2.70/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.70/0.98      | k1_xboole_0 = X0
% 2.70/0.98      | k1_xboole_0 = X1 ),
% 2.70/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_96,plain,
% 2.70/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.70/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_24,plain,
% 2.70/0.98      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 2.70/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_40,plain,
% 2.70/0.98      ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
% 2.70/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(c_42,plain,
% 2.70/0.98      ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.70/0.98      inference(instantiation,[status(thm)],[c_40]) ).
% 2.70/0.98  
% 2.70/0.98  cnf(contradiction,plain,
% 2.70/0.98      ( $false ),
% 2.70/0.98      inference(minisat,
% 2.70/0.98                [status(thm)],
% 2.70/0.98                [c_12157,c_12034,c_9912,c_9703,c_9090,c_9009,c_8974,
% 2.70/0.98                 c_8915,c_8677,c_8614,c_8591,c_8555,c_8545,c_8544,c_98,
% 2.70/0.98                 c_1,c_97,c_96,c_42]) ).
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  ------                               Statistics
% 2.70/0.98  
% 2.70/0.98  ------ General
% 2.70/0.98  
% 2.70/0.98  abstr_ref_over_cycles:                  0
% 2.70/0.98  abstr_ref_under_cycles:                 0
% 2.70/0.98  gc_basic_clause_elim:                   0
% 2.70/0.98  forced_gc_time:                         0
% 2.70/0.98  parsing_time:                           0.009
% 2.70/0.98  unif_index_cands_time:                  0.
% 2.70/0.98  unif_index_add_time:                    0.
% 2.70/0.98  orderings_time:                         0.
% 2.70/0.98  out_proof_time:                         0.007
% 2.70/0.98  total_time:                             0.254
% 2.70/0.98  num_of_symbols:                         53
% 2.70/0.98  num_of_terms:                           5776
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing
% 2.70/0.98  
% 2.70/0.98  num_of_splits:                          0
% 2.70/0.98  num_of_split_atoms:                     0
% 2.70/0.98  num_of_reused_defs:                     0
% 2.70/0.98  num_eq_ax_congr_red:                    52
% 2.70/0.98  num_of_sem_filtered_clauses:            1
% 2.70/0.98  num_of_subtypes:                        0
% 2.70/0.98  monotx_restored_types:                  0
% 2.70/0.98  sat_num_of_epr_types:                   0
% 2.70/0.98  sat_num_of_non_cyclic_types:            0
% 2.70/0.98  sat_guarded_non_collapsed_types:        0
% 2.70/0.98  num_pure_diseq_elim:                    0
% 2.70/0.98  simp_replaced_by:                       0
% 2.70/0.98  res_preprocessed:                       147
% 2.70/0.98  prep_upred:                             0
% 2.70/0.98  prep_unflattend:                        289
% 2.70/0.98  smt_new_axioms:                         0
% 2.70/0.98  pred_elim_cands:                        7
% 2.70/0.98  pred_elim:                              2
% 2.70/0.98  pred_elim_cl:                           2
% 2.70/0.98  pred_elim_cycles:                       14
% 2.70/0.98  merged_defs:                            0
% 2.70/0.98  merged_defs_ncl:                        0
% 2.70/0.98  bin_hyper_res:                          0
% 2.70/0.98  prep_cycles:                            4
% 2.70/0.98  pred_elim_time:                         0.116
% 2.70/0.98  splitting_time:                         0.
% 2.70/0.98  sem_filter_time:                        0.
% 2.70/0.98  monotx_time:                            0.
% 2.70/0.98  subtype_inf_time:                       0.
% 2.70/0.98  
% 2.70/0.98  ------ Problem properties
% 2.70/0.98  
% 2.70/0.98  clauses:                                30
% 2.70/0.98  conjectures:                            7
% 2.70/0.98  epr:                                    7
% 2.70/0.98  horn:                                   23
% 2.70/0.98  ground:                                 9
% 2.70/0.98  unary:                                  11
% 2.70/0.98  binary:                                 3
% 2.70/0.98  lits:                                   72
% 2.70/0.98  lits_eq:                                11
% 2.70/0.98  fd_pure:                                0
% 2.70/0.98  fd_pseudo:                              0
% 2.70/0.98  fd_cond:                                2
% 2.70/0.98  fd_pseudo_cond:                         1
% 2.70/0.98  ac_symbols:                             0
% 2.70/0.98  
% 2.70/0.98  ------ Propositional Solver
% 2.70/0.98  
% 2.70/0.98  prop_solver_calls:                      28
% 2.70/0.98  prop_fast_solver_calls:                 2602
% 2.70/0.98  smt_solver_calls:                       0
% 2.70/0.98  smt_fast_solver_calls:                  0
% 2.70/0.98  prop_num_of_clauses:                    2266
% 2.70/0.98  prop_preprocess_simplified:             8637
% 2.70/0.98  prop_fo_subsumed:                       52
% 2.70/0.98  prop_solver_time:                       0.
% 2.70/0.98  smt_solver_time:                        0.
% 2.70/0.98  smt_fast_solver_time:                   0.
% 2.70/0.98  prop_fast_solver_time:                  0.
% 2.70/0.98  prop_unsat_core_time:                   0.
% 2.70/0.98  
% 2.70/0.98  ------ QBF
% 2.70/0.98  
% 2.70/0.98  qbf_q_res:                              0
% 2.70/0.98  qbf_num_tautologies:                    0
% 2.70/0.98  qbf_prep_cycles:                        0
% 2.70/0.98  
% 2.70/0.98  ------ BMC1
% 2.70/0.98  
% 2.70/0.98  bmc1_current_bound:                     -1
% 2.70/0.98  bmc1_last_solved_bound:                 -1
% 2.70/0.98  bmc1_unsat_core_size:                   -1
% 2.70/0.98  bmc1_unsat_core_parents_size:           -1
% 2.70/0.98  bmc1_merge_next_fun:                    0
% 2.70/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation
% 2.70/0.98  
% 2.70/0.98  inst_num_of_clauses:                    715
% 2.70/0.98  inst_num_in_passive:                    395
% 2.70/0.98  inst_num_in_active:                     317
% 2.70/0.98  inst_num_in_unprocessed:                3
% 2.70/0.98  inst_num_of_loops:                      340
% 2.70/0.98  inst_num_of_learning_restarts:          0
% 2.70/0.98  inst_num_moves_active_passive:          21
% 2.70/0.98  inst_lit_activity:                      0
% 2.70/0.98  inst_lit_activity_moves:                0
% 2.70/0.98  inst_num_tautologies:                   0
% 2.70/0.98  inst_num_prop_implied:                  0
% 2.70/0.98  inst_num_existing_simplified:           0
% 2.70/0.98  inst_num_eq_res_simplified:             0
% 2.70/0.98  inst_num_child_elim:                    0
% 2.70/0.98  inst_num_of_dismatching_blockings:      218
% 2.70/0.98  inst_num_of_non_proper_insts:           450
% 2.70/0.98  inst_num_of_duplicates:                 0
% 2.70/0.98  inst_inst_num_from_inst_to_res:         0
% 2.70/0.98  inst_dismatching_checking_time:         0.
% 2.70/0.98  
% 2.70/0.98  ------ Resolution
% 2.70/0.98  
% 2.70/0.98  res_num_of_clauses:                     0
% 2.70/0.98  res_num_in_passive:                     0
% 2.70/0.98  res_num_in_active:                      0
% 2.70/0.98  res_num_of_loops:                       151
% 2.70/0.98  res_forward_subset_subsumed:            17
% 2.70/0.98  res_backward_subset_subsumed:           0
% 2.70/0.98  res_forward_subsumed:                   0
% 2.70/0.98  res_backward_subsumed:                  0
% 2.70/0.98  res_forward_subsumption_resolution:     6
% 2.70/0.98  res_backward_subsumption_resolution:    0
% 2.70/0.98  res_clause_to_clause_subsumption:       281
% 2.70/0.98  res_orphan_elimination:                 0
% 2.70/0.98  res_tautology_del:                      39
% 2.70/0.98  res_num_eq_res_simplified:              0
% 2.70/0.98  res_num_sel_changes:                    0
% 2.70/0.98  res_moves_from_active_to_pass:          0
% 2.70/0.98  
% 2.70/0.98  ------ Superposition
% 2.70/0.98  
% 2.70/0.98  sup_time_total:                         0.
% 2.70/0.98  sup_time_generating:                    0.
% 2.70/0.98  sup_time_sim_full:                      0.
% 2.70/0.98  sup_time_sim_immed:                     0.
% 2.70/0.98  
% 2.70/0.98  sup_num_of_clauses:                     90
% 2.70/0.98  sup_num_in_active:                      44
% 2.70/0.98  sup_num_in_passive:                     46
% 2.70/0.98  sup_num_of_loops:                       66
% 2.70/0.98  sup_fw_superposition:                   43
% 2.70/0.98  sup_bw_superposition:                   32
% 2.70/0.98  sup_immediate_simplified:               31
% 2.70/0.98  sup_given_eliminated:                   0
% 2.70/0.98  comparisons_done:                       0
% 2.70/0.98  comparisons_avoided:                    0
% 2.70/0.98  
% 2.70/0.98  ------ Simplifications
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  sim_fw_subset_subsumed:                 2
% 2.70/0.98  sim_bw_subset_subsumed:                 0
% 2.70/0.98  sim_fw_subsumed:                        0
% 2.70/0.98  sim_bw_subsumed:                        0
% 2.70/0.98  sim_fw_subsumption_res:                 0
% 2.70/0.98  sim_bw_subsumption_res:                 0
% 2.70/0.98  sim_tautology_del:                      0
% 2.70/0.98  sim_eq_tautology_del:                   8
% 2.70/0.98  sim_eq_res_simp:                        1
% 2.70/0.98  sim_fw_demodulated:                     11
% 2.70/0.98  sim_bw_demodulated:                     22
% 2.70/0.98  sim_light_normalised:                   18
% 2.70/0.98  sim_joinable_taut:                      0
% 2.70/0.98  sim_joinable_simp:                      0
% 2.70/0.98  sim_ac_normalised:                      0
% 2.70/0.98  sim_smt_subsumption:                    0
% 2.70/0.98  
%------------------------------------------------------------------------------
