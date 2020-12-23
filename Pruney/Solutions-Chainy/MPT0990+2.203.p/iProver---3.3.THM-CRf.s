%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:40 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 839 expanded)
%              Number of clauses        :   95 ( 219 expanded)
%              Number of leaves         :   15 ( 227 expanded)
%              Depth                    :   21
%              Number of atoms          :  751 (8180 expanded)
%              Number of equality atoms :  291 (2859 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK8
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK8),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK8,X1,X0)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK7) != X3
          & k1_xboole_0 != sK6
          & k1_xboole_0 != sK5
          & v2_funct_1(sK7)
          & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,X3),k6_partfun1(sK5))
          & k2_relset_1(sK5,sK6,sK7) = sK6
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
          & v1_funct_2(X3,sK6,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_funct_1(sK7) != sK8
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & v2_funct_1(sK7)
    & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5))
    & k2_relset_1(sK5,sK6,sK7) = sK6
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    & v1_funct_2(sK8,sK6,sK5)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f33,f32])).

fof(f58,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f10])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( r2_relset_1(X1,X3,X4,X5)
                  | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  | ~ v1_funct_2(X5,X1,X3)
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
              | ~ v1_funct_2(X4,X1,X3)
              | ~ v1_funct_1(X4) )
          | k1_xboole_0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_relset_1(X1,X3,X4,X5)
                    & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    & v1_funct_2(X5,X1,X3)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                & v1_funct_2(X4,X1,X3)
                & v1_funct_1(X4) )
            & k1_xboole_0 != X3 ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_relset_1(X0,X3,X4,X5)
                    & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                    & v1_funct_2(X5,X0,X3)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                & v1_funct_2(X4,X0,X3)
                & v1_funct_1(X4) )
            & k1_xboole_0 != X3 ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( r2_relset_1(X0,X6,X7,X8)
                    | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                    | ~ v1_funct_2(X8,X0,X6)
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                | ~ v1_funct_2(X7,X0,X6)
                | ~ v1_funct_1(X7) )
            | k1_xboole_0 = X6 )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(X0,X3,X4,X5)
          & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X5,X0,X3)
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(X0,X3,X4,sK4(X0,X1,X2))
        & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,sK4(X0,X1,X2)))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK4(X0,X1,X2),X0,X3)
        & v1_funct_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X0,X3,X4,X5)
              & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X5,X0,X3)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(X0,X3,sK3(X0,X1,X2),X5)
            & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,X3,X1,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X5,X0,X3)
            & v1_funct_1(X5) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK3(X0,X1,X2),X0,X3)
        & v1_funct_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_relset_1(X0,X3,X4,X5)
                  & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                  & v1_funct_2(X5,X0,X3)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
          & k1_xboole_0 != X3 )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X0,sK2(X0,X1,X2),X4,X5)
                & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X4),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
                & v1_funct_2(X5,X0,sK2(X0,X1,X2))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
            & v1_funct_2(X4,X0,sK2(X0,X1,X2))
            & v1_funct_1(X4) )
        & k1_xboole_0 != sK2(X0,X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_relset_1(X0,sK2(X0,X1,X2),sK3(X0,X1,X2),sK4(X0,X1,X2))
          & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK4(X0,X1,X2)))
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
          & v1_funct_2(sK4(X0,X1,X2),X0,sK2(X0,X1,X2))
          & v1_funct_1(sK4(X0,X1,X2))
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
          & v1_funct_2(sK3(X0,X1,X2),X0,sK2(X0,X1,X2))
          & v1_funct_1(sK3(X0,X1,X2))
          & k1_xboole_0 != sK2(X0,X1,X2) ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( r2_relset_1(X0,X6,X7,X8)
                    | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                    | ~ v1_funct_2(X8,X0,X6)
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                | ~ v1_funct_2(X7,X0,X6)
                | ~ v1_funct_1(X7) )
            | k1_xboole_0 = X6 )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f40,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( r2_relset_1(X0,X6,X7,X8)
      | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
      | ~ v1_funct_2(X8,X0,X6)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
      | ~ v1_funct_2(X7,X0,X6)
      | ~ v1_funct_1(X7)
      | k1_xboole_0 = X6
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v1_funct_2(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => ( k2_relset_1(X0,X1,X2) = X1
        <=> ! [X3] :
              ( k1_xboole_0 != X3
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    & v1_funct_2(X4,X1,X3)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                        & v1_funct_2(X5,X1,X3)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                       => r2_relset_1(X1,X3,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f13,f21,f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | k2_relset_1(X0,X1,X2) != X1 ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_relset_1(X0,X2,X1) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_relset_1(X0,X2,X1) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_relset_1(X0,X2,X1) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    k2_funct_1(sK7) != sK8 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2485,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_495,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK7,X0,X1)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_32])).

cnf(c_500,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_2478,plain,
    ( k2_relset_1(X0,X1,sK7) != X1
    | v1_funct_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2879,plain,
    ( v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2478])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2746,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_2747,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_3060,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2879,c_34,c_35,c_26,c_2747])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2503,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4463,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_2503])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_446,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_447,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK7))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( v1_funct_1(k2_funct_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK7,X0,X1)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_32])).

cnf(c_452,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK7))
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_2734,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_funct_1(k2_funct_1(sK7))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_2735,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2734])).

cnf(c_5258,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_34,c_35,c_26,c_2735])).

cnf(c_5259,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5258])).

cnf(c_5270,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k5_relat_1(sK7,k2_funct_1(sK7))
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_5259])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_392,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_393,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X0,X1,sK7) != X1
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK7,X0,X1)
    | k2_relset_1(X0,X1,sK7) != X1
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_32])).

cnf(c_398,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK7) != X1
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_2482,plain,
    ( k2_relset_1(X0,X1,sK7) != X1
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3357,plain,
    ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2482])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2737,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k2_relset_1(sK5,sK6,sK7) != sK6
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_3559,plain,
    ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3357,c_31,c_30,c_26,c_22,c_2737])).

cnf(c_5278,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5270,c_3559])).

cnf(c_33,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5339,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5278,c_33])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2488,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4461,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_2503])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4710,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4461,c_36])).

cnf(c_4711,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4710])).

cnf(c_4722,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_4711])).

cnf(c_2824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | k1_partfun1(X1,X2,X3,X4,X0,sK8) = k5_relat_1(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3031,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_3307,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X0,X1,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_3552,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3307])).

cnf(c_4781,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4722,c_32,c_30,c_29,c_27,c_3552])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X0,X0,X1,X5,X2),k1_partfun1(X4,X0,X0,X1,X5,X3))
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ sP0(X0,X5,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2491,plain,
    ( k1_xboole_0 = X0
    | r2_relset_1(X1,X0,X2,X3) = iProver_top
    | r2_relset_1(X4,X0,k1_partfun1(X4,X1,X1,X0,X5,X2),k1_partfun1(X4,X1,X1,X0,X5,X3)) != iProver_top
    | v1_funct_2(X2,X1,X0) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | sP0(X1,X5,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4786,plain,
    ( sK5 = k1_xboole_0
    | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | v1_funct_2(sK8,sK6,sK5) != iProver_top
    | sP0(sK6,sK7,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4781,c_2491])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,plain,
    ( v1_funct_2(sK8,sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1989,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2764,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_2934,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_1988,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2935,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | sP1(X1,X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2790,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | sP1(X0,sK7,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3001,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP1(sK5,sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_3002,plain,
    ( k1_xboole_0 = sK6
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | sP1(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3001])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | k2_relset_1(X0,X2,X1) != X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2501,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | sP1(X0,X2,X1) != iProver_top
    | sP0(X1,X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3875,plain,
    ( sP1(sK5,sK7,sK6) != iProver_top
    | sP0(sK6,sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2501])).

cnf(c_6045,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4786,c_33,c_34,c_35,c_36,c_37,c_38,c_23,c_22,c_2934,c_2935,c_3002,c_3875])).

cnf(c_6046,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6045])).

cnf(c_6057,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) = iProver_top
    | v1_funct_2(k2_funct_1(sK7),sK6,sK5) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5339,c_6046])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2489,plain,
    ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4784,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4781,c_2489])).

cnf(c_1,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2504,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4336,plain,
    ( sK8 = X0
    | r2_relset_1(sK6,sK5,sK8,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_2504])).

cnf(c_4405,plain,
    ( k2_funct_1(sK7) = sK8
    | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_4336])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_471,plain,
    ( v1_funct_2(k2_funct_1(sK7),X0,X1)
    | ~ v1_funct_2(sK7,X1,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK7,X1,X0)
    | v1_funct_2(k2_funct_1(sK7),X0,X1)
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_32])).

cnf(c_476,plain,
    ( v1_funct_2(k2_funct_1(sK7),X0,X1)
    | ~ v1_funct_2(sK7,X1,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_2743,plain,
    ( v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_2744,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(k2_funct_1(sK7),sK6,sK5) = iProver_top
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_21,negated_conjecture,
    ( k2_funct_1(sK7) != sK8 ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6057,c_4784,c_4405,c_2747,c_2744,c_2735,c_21,c_26,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.99  
% 2.59/0.99  ------  iProver source info
% 2.59/0.99  
% 2.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.99  git: non_committed_changes: false
% 2.59/0.99  git: last_make_outside_of_git: false
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     num_symb
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       true
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  ------ Parsing...
% 2.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.99  ------ Proving...
% 2.59/0.99  ------ Problem Properties 
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  clauses                                 32
% 2.59/0.99  conjectures                             11
% 2.59/0.99  EPR                                     6
% 2.59/0.99  Horn                                    21
% 2.59/0.99  unary                                   11
% 2.59/0.99  binary                                  10
% 2.59/0.99  lits                                    83
% 2.59/0.99  lits eq                                 20
% 2.59/0.99  fd_pure                                 0
% 2.59/0.99  fd_pseudo                               0
% 2.59/0.99  fd_cond                                 4
% 2.59/0.99  fd_pseudo_cond                          1
% 2.59/0.99  AC symbols                              0
% 2.59/0.99  
% 2.59/0.99  ------ Schedule dynamic 5 is on 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  Current options:
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     none
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       false
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ Proving...
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS status Theorem for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  fof(f6,conjecture,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f7,negated_conjecture,(
% 2.59/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.99    inference(negated_conjecture,[],[f6])).
% 2.59/0.99  
% 2.59/0.99  fof(f18,plain,(
% 2.59/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f7])).
% 2.59/0.99  
% 2.59/0.99  fof(f19,plain,(
% 2.59/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.59/0.99    inference(flattening,[],[f18])).
% 2.59/0.99  
% 2.59/0.99  fof(f33,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK8 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK8),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK8,X1,X0) & v1_funct_1(sK8))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f32,plain,(
% 2.59/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK7) != X3 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & v2_funct_1(sK7) & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,X3),k6_partfun1(sK5)) & k2_relset_1(sK5,sK6,sK7) = sK6 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) & v1_funct_2(X3,sK6,sK5) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f34,plain,(
% 2.59/0.99    (k2_funct_1(sK7) != sK8 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & v2_funct_1(sK7) & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) & k2_relset_1(sK5,sK6,sK7) = sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) & v1_funct_2(sK8,sK6,sK5) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f33,f32])).
% 2.59/0.99  
% 2.59/0.99  fof(f58,plain,(
% 2.59/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f62,plain,(
% 2.59/0.99    k2_relset_1(sK5,sK6,sK7) = sK6),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f4,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f14,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f4])).
% 2.59/0.99  
% 2.59/0.99  fof(f15,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.99    inference(flattening,[],[f14])).
% 2.59/0.99  
% 2.59/0.99  fof(f53,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f64,plain,(
% 2.59/0.99    v2_funct_1(sK7)),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f56,plain,(
% 2.59/0.99    v1_funct_1(sK7)),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f57,plain,(
% 2.59/0.99    v1_funct_2(sK7,sK5,sK6)),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f2,axiom,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f10,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.59/0.99    inference(ennf_transformation,[],[f2])).
% 2.59/0.99  
% 2.59/0.99  fof(f11,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.59/0.99    inference(flattening,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f37,plain,(
% 2.59/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  fof(f51,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f5,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f16,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f5])).
% 2.59/0.99  
% 2.59/0.99  fof(f17,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.99    inference(flattening,[],[f16])).
% 2.59/0.99  
% 2.59/0.99  fof(f54,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f17])).
% 2.59/0.99  
% 2.59/0.99  fof(f66,plain,(
% 2.59/0.99    k1_xboole_0 != sK6),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f61,plain,(
% 2.59/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f59,plain,(
% 2.59/0.99    v1_funct_1(sK8)),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f20,plain,(
% 2.59/0.99    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3))),
% 2.59/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.59/0.99  
% 2.59/0.99  fof(f26,plain,(
% 2.59/0.99    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X1,X3,X4,X5) & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3) | ~sP0(X1,X2,X0)))),
% 2.59/0.99    inference(nnf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f27,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | ~sP0(X0,X1,X2)))),
% 2.59/0.99    inference(rectify,[],[f26])).
% 2.59/0.99  
% 2.59/0.99  fof(f30,plain,(
% 2.59/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) => (~r2_relset_1(X0,X3,X4,sK4(X0,X1,X2)) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4(X0,X1,X2),X0,X3) & v1_funct_1(sK4(X0,X1,X2))))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f29,plain,(
% 2.59/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(X0,X3,sK3(X0,X1,X2),X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK3(X0,X1,X2),X0,X3) & v1_funct_1(sK3(X0,X1,X2))))) )),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f28,plain,(
% 2.59/0.99    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3) => (? [X4] : (? [X5] : (~r2_relset_1(X0,sK2(X0,X1,X2),X4,X5) & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X4),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(X5,X0,sK2(X0,X1,X2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(X4,X0,sK2(X0,X1,X2)) & v1_funct_1(X4)) & k1_xboole_0 != sK2(X0,X1,X2)))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f31,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_relset_1(X0,sK2(X0,X1,X2),sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(sK4(X0,X1,X2),X0,sK2(X0,X1,X2)) & v1_funct_1(sK4(X0,X1,X2))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(sK3(X0,X1,X2),X0,sK2(X0,X1,X2)) & v1_funct_1(sK3(X0,X1,X2))) & k1_xboole_0 != sK2(X0,X1,X2))) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | ~sP0(X0,X1,X2)))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 2.59/0.99  
% 2.59/0.99  fof(f40,plain,(
% 2.59/0.99    ( ! [X6,X2,X0,X8,X7,X1] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7) | k1_xboole_0 = X6 | ~sP0(X0,X1,X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f31])).
% 2.59/0.99  
% 2.59/0.99  fof(f60,plain,(
% 2.59/0.99    v1_funct_2(sK8,sK6,sK5)),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f65,plain,(
% 2.59/0.99    k1_xboole_0 != sK5),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f3,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => (k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (k1_xboole_0 != X3 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) => (r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) => r2_relset_1(X1,X3,X4,X5))))))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f12,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : ((r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4))) | k1_xboole_0 = X3)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.99    inference(ennf_transformation,[],[f3])).
% 2.59/0.99  
% 2.59/0.99  fof(f13,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.99    inference(flattening,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f21,plain,(
% 2.59/0.99    ! [X0,X2,X1] : ((k2_relset_1(X0,X1,X2) = X1 <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 2.59/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.59/0.99  
% 2.59/0.99  fof(f22,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (sP1(X0,X2,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.99    inference(definition_folding,[],[f13,f21,f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f50,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f24,plain,(
% 2.59/0.99    ! [X0,X2,X1] : (((k2_relset_1(X0,X1,X2) = X1 | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | k2_relset_1(X0,X1,X2) != X1)) | ~sP1(X0,X2,X1))),
% 2.59/0.99    inference(nnf_transformation,[],[f21])).
% 2.59/0.99  
% 2.59/0.99  fof(f25,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (((k2_relset_1(X0,X2,X1) = X2 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2)) | ~sP1(X0,X1,X2))),
% 2.59/0.99    inference(rectify,[],[f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f38,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2 | ~sP1(X0,X1,X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f25])).
% 2.59/0.99  
% 2.59/0.99  fof(f63,plain,(
% 2.59/0.99    r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5))),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f1,axiom,(
% 2.59/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f8,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.59/0.99    inference(ennf_transformation,[],[f1])).
% 2.59/0.99  
% 2.59/0.99  fof(f9,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(flattening,[],[f8])).
% 2.59/0.99  
% 2.59/0.99  fof(f23,plain,(
% 2.59/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(nnf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f35,plain,(
% 2.59/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f52,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f67,plain,(
% 2.59/0.99    k2_funct_1(sK7) != sK8),
% 2.59/0.99    inference(cnf_transformation,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  cnf(c_30,negated_conjecture,
% 2.59/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2485,plain,
% 2.59/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_26,negated_conjecture,
% 2.59/0.99      ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
% 2.59/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_16,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.59/0.99      | ~ v2_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_24,negated_conjecture,
% 2.59/0.99      ( v2_funct_1(sK7) ),
% 2.59/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_494,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.59/0.99      | sK7 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_495,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_32,negated_conjecture,
% 2.59/0.99      ( v1_funct_1(sK7) ),
% 2.59/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_499,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_495,c_32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_500,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_499]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2478,plain,
% 2.59/0.99      ( k2_relset_1(X0,X1,sK7) != X1
% 2.59/0.99      | v1_funct_2(sK7,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2879,plain,
% 2.59/0.99      ( v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_26,c_2478]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_31,negated_conjecture,
% 2.59/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 2.59/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_34,plain,
% 2.59/0.99      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_35,plain,
% 2.59/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2746,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_500]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2747,plain,
% 2.59/0.99      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.59/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3060,plain,
% 2.59/0.99      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_2879,c_34,c_35,c_26,c_2747]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(X3)
% 2.59/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2503,plain,
% 2.59/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.59/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.59/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | v1_funct_1(X5) != iProver_top
% 2.59/0.99      | v1_funct_1(X4) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4463,plain,
% 2.59/0.99      ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | v1_funct_1(X2) != iProver_top
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3060,c_2503]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_18,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v2_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_446,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.59/0.99      | sK7 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_447,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_451,plain,
% 2.59/0.99      ( v1_funct_1(k2_funct_1(sK7))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_447,c_32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_452,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7))
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_451]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2734,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7))
% 2.59/0.99      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_452]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2735,plain,
% 2.59/0.99      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.59/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2734]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5258,plain,
% 2.59/0.99      ( v1_funct_1(X2) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7)) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_4463,c_34,c_35,c_26,c_2735]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5259,plain,
% 2.59/0.99      ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_5258]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5270,plain,
% 2.59/0.99      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k5_relat_1(sK7,k2_funct_1(sK7))
% 2.59/0.99      | v1_funct_1(sK7) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2485,c_5259]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_20,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v2_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.59/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_392,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.59/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.59/0.99      | sK7 != X0
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_393,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1
% 2.59/0.99      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_397,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1
% 2.59/0.99      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_393,c_32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_398,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | k2_relset_1(X0,X1,sK7) != X1
% 2.59/0.99      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_397]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2482,plain,
% 2.59/0.99      ( k2_relset_1(X0,X1,sK7) != X1
% 2.59/0.99      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(X0)
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | v1_funct_2(sK7,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3357,plain,
% 2.59/0.99      ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
% 2.59/0.99      | sK6 = k1_xboole_0
% 2.59/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_26,c_2482]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_22,negated_conjecture,
% 2.59/0.99      ( k1_xboole_0 != sK6 ),
% 2.59/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2737,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | k2_relset_1(sK5,sK6,sK7) != sK6
% 2.59/0.99      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
% 2.59/0.99      | k1_xboole_0 = sK6 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_398]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3559,plain,
% 2.59/0.99      ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_3357,c_31,c_30,c_26,c_22,c_2737]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5278,plain,
% 2.59/0.99      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5)
% 2.59/0.99      | v1_funct_1(sK7) != iProver_top ),
% 2.59/0.99      inference(light_normalisation,[status(thm)],[c_5270,c_3559]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_33,plain,
% 2.59/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5339,plain,
% 2.59/0.99      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_5278,c_33]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_27,negated_conjecture,
% 2.59/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2488,plain,
% 2.59/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4461,plain,
% 2.59/0.99      ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | v1_funct_1(X2) != iProver_top
% 2.59/0.99      | v1_funct_1(sK8) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2488,c_2503]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_29,negated_conjecture,
% 2.59/0.99      ( v1_funct_1(sK8) ),
% 2.59/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_36,plain,
% 2.59/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4710,plain,
% 2.59/0.99      ( v1_funct_1(X2) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_4461,c_36]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4711,plain,
% 2.59/0.99      ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.59/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_4710]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4722,plain,
% 2.59/0.99      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8)
% 2.59/0.99      | v1_funct_1(sK7) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2485,c_4711]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2824,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(sK8)
% 2.59/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK8) = k5_relat_1(X0,sK8) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3031,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.59/0.99      | ~ v1_funct_1(sK8)
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2824]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3307,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_1(sK8)
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k1_partfun1(X0,X1,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3031]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3552,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | ~ v1_funct_1(sK8)
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3307]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4781,plain,
% 2.59/0.99      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_4722,c_32,c_30,c_29,c_27,c_3552]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_14,plain,
% 2.59/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 2.59/0.99      | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X0,X0,X1,X5,X2),k1_partfun1(X4,X0,X0,X1,X5,X3))
% 2.59/0.99      | ~ v1_funct_2(X3,X0,X1)
% 2.59/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.59/0.99      | ~ sP0(X0,X5,X4)
% 2.59/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_1(X3)
% 2.59/0.99      | ~ v1_funct_1(X2)
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2491,plain,
% 2.59/0.99      ( k1_xboole_0 = X0
% 2.59/0.99      | r2_relset_1(X1,X0,X2,X3) = iProver_top
% 2.59/0.99      | r2_relset_1(X4,X0,k1_partfun1(X4,X1,X1,X0,X5,X2),k1_partfun1(X4,X1,X1,X0,X5,X3)) != iProver_top
% 2.59/0.99      | v1_funct_2(X2,X1,X0) != iProver_top
% 2.59/0.99      | v1_funct_2(X3,X1,X0) != iProver_top
% 2.59/0.99      | sP0(X1,X5,X4) != iProver_top
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.59/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.59/0.99      | v1_funct_1(X2) != iProver_top
% 2.59/0.99      | v1_funct_1(X3) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4786,plain,
% 2.59/0.99      ( sK5 = k1_xboole_0
% 2.59/0.99      | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.59/0.99      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.59/0.99      | v1_funct_2(sK8,sK6,sK5) != iProver_top
% 2.59/0.99      | sP0(sK6,sK7,sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.59/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.59/0.99      | v1_funct_1(X0) != iProver_top
% 2.59/0.99      | v1_funct_1(sK8) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_4781,c_2491]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_28,negated_conjecture,
% 2.59/0.99      ( v1_funct_2(sK8,sK6,sK5) ),
% 2.59/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_37,plain,
% 2.59/0.99      ( v1_funct_2(sK8,sK6,sK5) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_38,plain,
% 2.59/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_23,negated_conjecture,
% 2.59/0.99      ( k1_xboole_0 != sK5 ),
% 2.59/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1989,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2764,plain,
% 2.59/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1989]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2934,plain,
% 2.59/0.99      ( sK5 != k1_xboole_0
% 2.59/0.99      | k1_xboole_0 = sK5
% 2.59/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2764]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1988,plain,( X0 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2935,plain,
% 2.59/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1988]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_15,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | sP1(X1,X0,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2790,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,X0,X1)
% 2.59/0.99      | sP1(X0,sK7,X1)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3001,plain,
% 2.59/0.99      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.59/0.99      | sP1(sK5,sK7,sK6)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k1_xboole_0 = sK6 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2790]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3002,plain,
% 2.59/0.99      ( k1_xboole_0 = sK6
% 2.59/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | sP1(sK5,sK7,sK6) = iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.59/0.99      | v1_funct_1(sK7) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3001]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4,plain,
% 2.59/0.99      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2501,plain,
% 2.59/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 2.59/0.99      | sP1(X0,X2,X1) != iProver_top
% 2.59/0.99      | sP0(X1,X2,X0) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3875,plain,
% 2.59/0.99      ( sP1(sK5,sK7,sK6) != iProver_top
% 2.59/0.99      | sP0(sK6,sK7,sK5) = iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_26,c_2501]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6045,plain,
% 2.59/0.99      ( v1_funct_1(X0) != iProver_top
% 2.59/0.99      | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.59/0.99      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_4786,c_33,c_34,c_35,c_36,c_37,c_38,c_23,c_22,c_2934,
% 2.59/0.99                 c_2935,c_3002,c_3875]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6046,plain,
% 2.59/0.99      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.59/0.99      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.59/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_6045]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6057,plain,
% 2.59/0.99      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) != iProver_top
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) = iProver_top
% 2.59/0.99      | v1_funct_2(k2_funct_1(sK7),sK6,sK5) != iProver_top
% 2.59/0.99      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.59/0.99      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5339,c_6046]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_25,negated_conjecture,
% 2.59/0.99      ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
% 2.59/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2489,plain,
% 2.59/0.99      ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4784,plain,
% 2.59/0.99      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_4781,c_2489]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1,plain,
% 2.59/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.59/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | X2 = X3 ),
% 2.59/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2504,plain,
% 2.59/0.99      ( X0 = X1
% 2.59/0.99      | r2_relset_1(X2,X3,X0,X1) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.59/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4336,plain,
% 2.59/0.99      ( sK8 = X0
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,X0) != iProver_top
% 2.59/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_2488,c_2504]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4405,plain,
% 2.59/0.99      ( k2_funct_1(sK7) = sK8
% 2.59/0.99      | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3060,c_4336]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_17,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v2_funct_1(X0)
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_470,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ v1_funct_1(X0)
% 2.59/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.59/0.99      | sK7 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_471,plain,
% 2.59/0.99      ( v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.59/0.99      | ~ v1_funct_2(sK7,X1,X0)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | ~ v1_funct_1(sK7)
% 2.59/0.99      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_475,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | ~ v1_funct_2(sK7,X1,X0)
% 2.59/0.99      | v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.59/0.99      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_471,c_32]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_476,plain,
% 2.59/0.99      ( v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.59/0.99      | ~ v1_funct_2(sK7,X1,X0)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.59/0.99      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_475]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2743,plain,
% 2.59/0.99      ( v1_funct_2(k2_funct_1(sK7),sK6,sK5)
% 2.59/0.99      | ~ v1_funct_2(sK7,sK5,sK6)
% 2.59/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.59/0.99      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2744,plain,
% 2.59/0.99      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.59/0.99      | v1_funct_2(k2_funct_1(sK7),sK6,sK5) = iProver_top
% 2.59/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.59/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_21,negated_conjecture,
% 2.59/0.99      ( k2_funct_1(sK7) != sK8 ),
% 2.59/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(contradiction,plain,
% 2.59/0.99      ( $false ),
% 2.59/0.99      inference(minisat,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_6057,c_4784,c_4405,c_2747,c_2744,c_2735,c_21,c_26,
% 2.59/0.99                 c_35,c_34]) ).
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  ------                               Statistics
% 2.59/0.99  
% 2.59/0.99  ------ General
% 2.59/0.99  
% 2.59/0.99  abstr_ref_over_cycles:                  0
% 2.59/0.99  abstr_ref_under_cycles:                 0
% 2.59/0.99  gc_basic_clause_elim:                   0
% 2.59/0.99  forced_gc_time:                         0
% 2.59/0.99  parsing_time:                           0.011
% 2.59/0.99  unif_index_cands_time:                  0.
% 2.59/0.99  unif_index_add_time:                    0.
% 2.59/0.99  orderings_time:                         0.
% 2.59/0.99  out_proof_time:                         0.011
% 2.59/0.99  total_time:                             0.209
% 2.59/0.99  num_of_symbols:                         53
% 2.59/0.99  num_of_terms:                           5471
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing
% 2.59/0.99  
% 2.59/0.99  num_of_splits:                          0
% 2.59/0.99  num_of_split_atoms:                     0
% 2.59/0.99  num_of_reused_defs:                     0
% 2.59/0.99  num_eq_ax_congr_red:                    45
% 2.59/0.99  num_of_sem_filtered_clauses:            1
% 2.59/0.99  num_of_subtypes:                        0
% 2.59/0.99  monotx_restored_types:                  0
% 2.59/0.99  sat_num_of_epr_types:                   0
% 2.59/0.99  sat_num_of_non_cyclic_types:            0
% 2.59/0.99  sat_guarded_non_collapsed_types:        0
% 2.59/0.99  num_pure_diseq_elim:                    0
% 2.59/0.99  simp_replaced_by:                       0
% 2.59/0.99  res_preprocessed:                       156
% 2.59/0.99  prep_upred:                             0
% 2.59/0.99  prep_unflattend:                        131
% 2.59/0.99  smt_new_axioms:                         0
% 2.59/0.99  pred_elim_cands:                        6
% 2.59/0.99  pred_elim:                              1
% 2.59/0.99  pred_elim_cl:                           1
% 2.59/0.99  pred_elim_cycles:                       5
% 2.59/0.99  merged_defs:                            0
% 2.59/0.99  merged_defs_ncl:                        0
% 2.59/0.99  bin_hyper_res:                          0
% 2.59/0.99  prep_cycles:                            4
% 2.59/0.99  pred_elim_time:                         0.031
% 2.59/0.99  splitting_time:                         0.
% 2.59/0.99  sem_filter_time:                        0.
% 2.59/0.99  monotx_time:                            0.
% 2.59/0.99  subtype_inf_time:                       0.
% 2.59/0.99  
% 2.59/0.99  ------ Problem properties
% 2.59/0.99  
% 2.59/0.99  clauses:                                32
% 2.59/0.99  conjectures:                            11
% 2.59/0.99  epr:                                    6
% 2.59/0.99  horn:                                   21
% 2.59/0.99  ground:                                 11
% 2.59/0.99  unary:                                  11
% 2.59/0.99  binary:                                 10
% 2.59/0.99  lits:                                   83
% 2.59/0.99  lits_eq:                                20
% 2.59/0.99  fd_pure:                                0
% 2.59/0.99  fd_pseudo:                              0
% 2.59/0.99  fd_cond:                                4
% 2.59/0.99  fd_pseudo_cond:                         1
% 2.59/0.99  ac_symbols:                             0
% 2.59/0.99  
% 2.59/0.99  ------ Propositional Solver
% 2.59/0.99  
% 2.59/0.99  prop_solver_calls:                      28
% 2.59/0.99  prop_fast_solver_calls:                 1457
% 2.59/0.99  smt_solver_calls:                       0
% 2.59/0.99  smt_fast_solver_calls:                  0
% 2.59/0.99  prop_num_of_clauses:                    1781
% 2.59/0.99  prop_preprocess_simplified:             6295
% 2.59/0.99  prop_fo_subsumed:                       56
% 2.59/0.99  prop_solver_time:                       0.
% 2.59/0.99  smt_solver_time:                        0.
% 2.59/0.99  smt_fast_solver_time:                   0.
% 2.59/0.99  prop_fast_solver_time:                  0.
% 2.59/0.99  prop_unsat_core_time:                   0.
% 2.59/0.99  
% 2.59/0.99  ------ QBF
% 2.59/0.99  
% 2.59/0.99  qbf_q_res:                              0
% 2.59/0.99  qbf_num_tautologies:                    0
% 2.59/0.99  qbf_prep_cycles:                        0
% 2.59/0.99  
% 2.59/0.99  ------ BMC1
% 2.59/0.99  
% 2.59/0.99  bmc1_current_bound:                     -1
% 2.59/0.99  bmc1_last_solved_bound:                 -1
% 2.59/0.99  bmc1_unsat_core_size:                   -1
% 2.59/0.99  bmc1_unsat_core_parents_size:           -1
% 2.59/0.99  bmc1_merge_next_fun:                    0
% 2.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation
% 2.59/0.99  
% 2.59/0.99  inst_num_of_clauses:                    514
% 2.59/0.99  inst_num_in_passive:                    15
% 2.59/0.99  inst_num_in_active:                     369
% 2.59/0.99  inst_num_in_unprocessed:                130
% 2.59/0.99  inst_num_of_loops:                      380
% 2.59/0.99  inst_num_of_learning_restarts:          0
% 2.59/0.99  inst_num_moves_active_passive:          8
% 2.59/0.99  inst_lit_activity:                      0
% 2.59/0.99  inst_lit_activity_moves:                0
% 2.59/0.99  inst_num_tautologies:                   0
% 2.59/0.99  inst_num_prop_implied:                  0
% 2.59/0.99  inst_num_existing_simplified:           0
% 2.59/0.99  inst_num_eq_res_simplified:             0
% 2.59/0.99  inst_num_child_elim:                    0
% 2.59/0.99  inst_num_of_dismatching_blockings:      45
% 2.59/0.99  inst_num_of_non_proper_insts:           549
% 2.59/0.99  inst_num_of_duplicates:                 0
% 2.59/0.99  inst_inst_num_from_inst_to_res:         0
% 2.59/0.99  inst_dismatching_checking_time:         0.
% 2.59/0.99  
% 2.59/0.99  ------ Resolution
% 2.59/0.99  
% 2.59/0.99  res_num_of_clauses:                     0
% 2.59/0.99  res_num_in_passive:                     0
% 2.59/0.99  res_num_in_active:                      0
% 2.59/0.99  res_num_of_loops:                       160
% 2.59/0.99  res_forward_subset_subsumed:            55
% 2.59/0.99  res_backward_subset_subsumed:           0
% 2.59/0.99  res_forward_subsumed:                   0
% 2.59/0.99  res_backward_subsumed:                  0
% 2.59/0.99  res_forward_subsumption_resolution:     0
% 2.59/0.99  res_backward_subsumption_resolution:    0
% 2.59/0.99  res_clause_to_clause_subsumption:       554
% 2.59/0.99  res_orphan_elimination:                 0
% 2.59/0.99  res_tautology_del:                      54
% 2.59/0.99  res_num_eq_res_simplified:              0
% 2.59/0.99  res_num_sel_changes:                    0
% 2.59/0.99  res_moves_from_active_to_pass:          0
% 2.59/0.99  
% 2.59/0.99  ------ Superposition
% 2.59/0.99  
% 2.59/0.99  sup_time_total:                         0.
% 2.59/0.99  sup_time_generating:                    0.
% 2.59/0.99  sup_time_sim_full:                      0.
% 2.59/0.99  sup_time_sim_immed:                     0.
% 2.59/0.99  
% 2.59/0.99  sup_num_of_clauses:                     108
% 2.59/0.99  sup_num_in_active:                      73
% 2.59/0.99  sup_num_in_passive:                     35
% 2.59/0.99  sup_num_of_loops:                       75
% 2.59/0.99  sup_fw_superposition:                   49
% 2.59/0.99  sup_bw_superposition:                   31
% 2.59/0.99  sup_immediate_simplified:               4
% 2.59/0.99  sup_given_eliminated:                   0
% 2.59/0.99  comparisons_done:                       0
% 2.59/0.99  comparisons_avoided:                    0
% 2.59/0.99  
% 2.59/0.99  ------ Simplifications
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  sim_fw_subset_subsumed:                 2
% 2.59/0.99  sim_bw_subset_subsumed:                 0
% 2.59/0.99  sim_fw_subsumed:                        0
% 2.59/0.99  sim_bw_subsumed:                        0
% 2.59/0.99  sim_fw_subsumption_res:                 0
% 2.59/0.99  sim_bw_subsumption_res:                 0
% 2.59/0.99  sim_tautology_del:                      0
% 2.59/0.99  sim_eq_tautology_del:                   5
% 2.59/0.99  sim_eq_res_simp:                        0
% 2.59/0.99  sim_fw_demodulated:                     0
% 2.59/0.99  sim_bw_demodulated:                     3
% 2.59/0.99  sim_light_normalised:                   2
% 2.59/0.99  sim_joinable_taut:                      0
% 2.59/0.99  sim_joinable_simp:                      0
% 2.59/0.99  sim_ac_normalised:                      0
% 2.59/0.99  sim_smt_subsumption:                    0
% 2.59/0.99  
%------------------------------------------------------------------------------
