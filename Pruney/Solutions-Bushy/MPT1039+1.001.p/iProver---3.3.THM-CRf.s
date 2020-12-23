%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1039+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:44 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   95 (1608 expanded)
%              Number of clauses        :   60 ( 487 expanded)
%              Number of leaves         :    7 ( 394 expanded)
%              Depth                    :   19
%              Number of atoms          :  422 (12687 expanded)
%              Number of equality atoms :  148 (2343 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
     => ( r1_partfun1(X0,sK1(X0,X1,X2,X3))
        & r1_partfun1(X1,sK1(X0,X1,X2,X3))
        & v1_partfun1(sK1(X0,X1,X2,X3),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_partfun1(X0,sK1(X0,X1,X2,X3))
        & r1_partfun1(X1,sK1(X0,X1,X2,X3))
        & v1_partfun1(sK1(X0,X1,X2,X3),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK1(X0,X1,X2,X3)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X0,sK1(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X1,sK1(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f5])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( ~ r1_partfun1(sK5,X4)
            | ~ r1_partfun1(X2,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X4,X0,X1)
            | ~ v1_funct_1(X4) )
        & r1_partfun1(X2,sK5)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_partfun1(X3,X4)
                | ~ r1_partfun1(X2,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X4,X0,X1)
                | ~ v1_funct_1(X4) )
            & r1_partfun1(X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(sK4,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
              | ~ v1_funct_2(X4,sK2,sK3)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(sK4,X3)
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK5,X4)
        | ~ r1_partfun1(sK4,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X4,sK2,sK3)
        | ~ v1_funct_1(X4) )
    & r1_partfun1(sK4,sK5)
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f18,f17])).

fof(f35,plain,(
    ! [X4] :
      ( ~ r1_partfun1(sK5,X4)
      | ~ r1_partfun1(sK4,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(X4,sK2,sK3)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK1(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK1(X0,X1,X2,X3),X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP0(X3,X2,X0,X1)
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f8,f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X0,X1)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X0,X1)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,k1_xboole_0,X1)
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f28])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X0,sK1(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1252,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,sK1(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X1,sK1(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1251,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X1,sK1(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1249,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( ~ v1_funct_2(X0,sK2,sK3)
    | ~ r1_partfun1(sK4,X0)
    | ~ r1_partfun1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_187,plain,
    ( ~ r1_partfun1(sK4,X0)
    | ~ r1_partfun1(sK5,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 != X1
    | sK3 != X3
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_188,plain,
    ( ~ r1_partfun1(sK4,X0)
    | ~ r1_partfun1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_1240,plain,
    ( r1_partfun1(sK4,X0) != iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_partfun1(X0,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_2087,plain,
    ( sP0(X0,X1,sK2,sK3) != iProver_top
    | r1_partfun1(sK4,sK1(X0,X1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK5,sK1(X0,X1,sK2,sK3)) != iProver_top
    | v1_partfun1(sK1(X0,X1,sK2,sK3),sK2) != iProver_top
    | v1_funct_1(sK1(X0,X1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1240])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_funct_1(sK1(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1248,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_funct_1(sK1(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_partfun1(sK1(X0,X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1250,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK1(X0,X1,X2,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2698,plain,
    ( sP0(X0,X1,sK2,sK3) != iProver_top
    | r1_partfun1(sK4,sK1(X0,X1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK5,sK1(X0,X1,sK2,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2087,c_1248,c_1250])).

cnf(c_2703,plain,
    ( sP0(X0,sK4,sK2,sK3) != iProver_top
    | r1_partfun1(sK5,sK1(X0,sK4,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_2698])).

cnf(c_2730,plain,
    ( sP0(sK5,sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_2703])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1242,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1244,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1246,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) = iProver_top
    | r1_partfun1(X2,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1609,plain,
    ( sK3 = k1_xboole_0
    | sP0(X0,sK5,sK2,sK3) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1246])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1938,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | sP0(X0,sK5,sK2,sK3) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_18])).

cnf(c_1939,plain,
    ( sK3 = k1_xboole_0
    | sP0(X0,sK5,sK2,sK3) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1938])).

cnf(c_1950,plain,
    ( sK3 = k1_xboole_0
    | sP0(sK4,sK5,sK2,sK3) = iProver_top
    | r1_partfun1(sK5,sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1939])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1978,plain,
    ( r1_partfun1(sK5,sK4) != iProver_top
    | sP0(sK4,sK5,sK2,sK3) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_16])).

cnf(c_1979,plain,
    ( sK3 = k1_xboole_0
    | sP0(sK4,sK5,sK2,sK3) = iProver_top
    | r1_partfun1(sK5,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1978])).

cnf(c_2702,plain,
    ( sP0(sK4,X0,sK2,sK3) != iProver_top
    | r1_partfun1(sK5,sK1(sK4,X0,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_2698])).

cnf(c_2721,plain,
    ( sP0(sK4,sK5,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_2702])).

cnf(c_2734,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1979,c_2721])).

cnf(c_1610,plain,
    ( sK3 = k1_xboole_0
    | sP0(X0,sK4,sK2,sK3) = iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1246])).

cnf(c_1986,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | sP0(X0,sK4,sK2,sK3) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_16])).

cnf(c_1987,plain,
    ( sK3 = k1_xboole_0
    | sP0(X0,sK4,sK2,sK3) = iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1986])).

cnf(c_1997,plain,
    ( sK3 = k1_xboole_0
    | sP0(sK5,sK4,sK2,sK3) = iProver_top
    | r1_partfun1(sK4,sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1987])).

cnf(c_10,negated_conjecture,
    ( r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,plain,
    ( r1_partfun1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2018,plain,
    ( sK3 = k1_xboole_0
    | sP0(sK5,sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1997,c_18,c_20])).

cnf(c_2737,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_2018,c_2730])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2747,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2737,c_11])).

cnf(c_2748,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2747])).

cnf(c_2868,plain,
    ( sP0(sK5,sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2730,c_2737,c_2748])).

cnf(c_2745,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2737,c_1244])).

cnf(c_2754,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2745,c_2748])).

cnf(c_2746,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2737,c_1242])).

cnf(c_2751,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2746,c_2748])).

cnf(c_7,plain,
    ( sP0(X0,X1,k1_xboole_0,X2)
    | ~ r1_partfun1(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1400,plain,
    ( sP0(X0,sK4,k1_xboole_0,X1)
    | ~ r1_partfun1(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1471,plain,
    ( sP0(sK5,sK4,k1_xboole_0,X0)
    | ~ r1_partfun1(sK4,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1472,plain,
    ( sP0(sK5,sK4,k1_xboole_0,X0) = iProver_top
    | r1_partfun1(sK4,sK5) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_1474,plain,
    ( sP0(sK5,sK4,k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_partfun1(sK4,sK5) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2868,c_2754,c_2751,c_1474,c_20,c_18,c_16])).


%------------------------------------------------------------------------------
