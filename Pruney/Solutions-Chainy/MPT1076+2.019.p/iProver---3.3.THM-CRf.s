%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:24 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  232 (2998 expanded)
%              Number of clauses        :  156 ( 824 expanded)
%              Number of leaves         :   22 (1079 expanded)
%              Depth                    :   24
%              Number of atoms          :  927 (23075 expanded)
%              Number of equality atoms :  372 (3590 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f47,f46,f45,f44,f43])).

fof(f78,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1317,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1316,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1314,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1325,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1322,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3653,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1322])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1323,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1324,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16977,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3653,c_1323,c_1324])).

cnf(c_16985,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_16977])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17209,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16985,c_33,c_34,c_35])).

cnf(c_17221,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_17209])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1677,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X3,X0,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1871,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k8_funct_2(X0,X1,X2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_2368,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_3421,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_3422,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3421])).

cnf(c_1697,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1931,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k8_funct_2(X0,X1,X2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2378,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | m1_subset_1(k8_funct_2(sK1,sK0,X0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_3454,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_3455,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3454])).

cnf(c_1707,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,sK4),X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1951,plain,
    ( v1_funct_2(k8_funct_2(X0,X1,X2,sK3,sK4),X0,X2)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_2409,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,X0,sK3,sK4),sK1,X0)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_3457,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_3458,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) = iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3457])).

cnf(c_4310,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X2) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_16946,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_4310])).

cnf(c_16947,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16946])).

cnf(c_17282,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17221,c_33,c_34,c_35,c_36,c_37,c_38,c_3422,c_3455,c_3458,c_16947])).

cnf(c_17283,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17282])).

cnf(c_17291,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1317,c_17283])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1321,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3652,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1321])).

cnf(c_15963,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3652,c_1323,c_1324])).

cnf(c_15971,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_15963])).

cnf(c_16181,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15971,c_33,c_34,c_35])).

cnf(c_16182,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_16181])).

cnf(c_16194,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_16182])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_425,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_427,plain,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_31])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_1307,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1994,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1307])).

cnf(c_16363,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16194,c_37,c_1994])).

cnf(c_16372,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1317,c_16363])).

cnf(c_17329,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_17291,c_16372])).

cnf(c_2572,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1322])).

cnf(c_2689,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2572,c_33,c_34,c_35])).

cnf(c_2697,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1317,c_2689])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1326,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2796,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_1326])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3465,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2796,c_33,c_34,c_35,c_36,c_39])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_332,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_1309,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2777,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1309])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1762,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_1763,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1779,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1780,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_3152,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2777,c_38,c_1763,c_1780])).

cnf(c_1330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2392,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1330])).

cnf(c_2640,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2392,c_38,c_1763,c_1780])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_411,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_412,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_412])).

cnf(c_451,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_807,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_451])).

cnf(c_1305,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_2645,plain,
    ( k1_relat_1(sK4) = sK0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2640,c_1305])).

cnf(c_839,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_806,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_451])).

cnf(c_1306,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_2033,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1306])).

cnf(c_2724,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_38,c_839,c_1763,c_1780,c_2033])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1318,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2729,plain,
    ( v1_funct_2(sK4,sK0,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_1318])).

cnf(c_3793,plain,
    ( v1_funct_2(sK4,sK0,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2729,c_37,c_38,c_1763,c_1780])).

cnf(c_3801,plain,
    ( v1_funct_2(sK4,sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3152,c_3793])).

cnf(c_2963,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1321])).

cnf(c_32,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3243,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2963,c_32,c_37,c_1994])).

cnf(c_3244,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3243])).

cnf(c_3924,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_3244])).

cnf(c_4515,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3465,c_3924])).

cnf(c_2571,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1322])).

cnf(c_2654,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_32,c_37])).

cnf(c_3925,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_2654])).

cnf(c_3944,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3465,c_3925])).

cnf(c_4918,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_4515,c_3944])).

cnf(c_22,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2699,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2697,c_22])).

cnf(c_4920,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_4918,c_2699])).

cnf(c_16391,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_16372,c_4920])).

cnf(c_17333,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_17329,c_16391])).

cnf(c_811,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1577,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_16354,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1328,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2133,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1316,c_1328])).

cnf(c_2727,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_2724,c_2133])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1327,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1905,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1314,c_1327])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k7_partfun1(X3,X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1320,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k7_partfun1(X2,X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3534,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_1320])).

cnf(c_4651,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3534,c_32,c_34,c_35,c_36])).

cnf(c_4652,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4651])).

cnf(c_4663,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_4652])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_1766,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_1782,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1783,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1782])).

cnf(c_2778,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1309])).

cnf(c_5837,plain,
    ( sK1 = k1_xboole_0
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4663,c_36,c_37,c_38,c_1766,c_1783,c_2778])).

cnf(c_5838,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5837])).

cnf(c_5847,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1317,c_5838])).

cnf(c_5850,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5847,c_4918])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17333,c_16354,c_5850,c_0,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.49/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.49  
% 7.49/1.49  ------  iProver source info
% 7.49/1.49  
% 7.49/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.49  git: non_committed_changes: false
% 7.49/1.49  git: last_make_outside_of_git: false
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    --mode clausify
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         false
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     num_symb
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       true
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     false
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   []
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_full_bw                           [BwDemod]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  ------ Parsing...
% 7.49/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.49  ------ Proving...
% 7.49/1.49  ------ Problem Properties 
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  clauses                                 28
% 7.49/1.49  conjectures                             9
% 7.49/1.49  EPR                                     7
% 7.49/1.49  Horn                                    23
% 7.49/1.49  unary                                   11
% 7.49/1.49  binary                                  4
% 7.49/1.49  lits                                    87
% 7.49/1.49  lits eq                                 8
% 7.49/1.49  fd_pure                                 0
% 7.49/1.49  fd_pseudo                               0
% 7.49/1.49  fd_cond                                 1
% 7.49/1.49  fd_pseudo_cond                          0
% 7.49/1.49  AC symbols                              0
% 7.49/1.49  
% 7.49/1.49  ------ Schedule dynamic 5 is on 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  Current options:
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    --mode clausify
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         false
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     none
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       false
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     false
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   []
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_full_bw                           [BwDemod]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ Proving...
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  % SZS status Theorem for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  fof(f16,conjecture,(
% 7.49/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f17,negated_conjecture,(
% 7.49/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 7.49/1.49    inference(negated_conjecture,[],[f16])).
% 7.49/1.49  
% 7.49/1.49  fof(f39,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f17])).
% 7.49/1.49  
% 7.49/1.49  fof(f40,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f39])).
% 7.49/1.49  
% 7.49/1.49  fof(f47,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f46,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f45,plain,(
% 7.49/1.49    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f44,plain,(
% 7.49/1.49    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f43,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f48,plain,(
% 7.49/1.49    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f47,f46,f45,f44,f43])).
% 7.49/1.49  
% 7.49/1.49  fof(f78,plain,(
% 7.49/1.49    m1_subset_1(sK5,sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f77,plain,(
% 7.49/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f75,plain,(
% 7.49/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f11,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f29,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.49/1.49    inference(ennf_transformation,[],[f11])).
% 7.49/1.49  
% 7.49/1.49  fof(f30,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.49/1.49    inference(flattening,[],[f29])).
% 7.49/1.49  
% 7.49/1.49  fof(f64,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f30])).
% 7.49/1.49  
% 7.49/1.49  fof(f12,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f31,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f12])).
% 7.49/1.49  
% 7.49/1.49  fof(f32,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f31])).
% 7.49/1.49  
% 7.49/1.49  fof(f65,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f32])).
% 7.49/1.49  
% 7.49/1.49  fof(f62,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f30])).
% 7.49/1.49  
% 7.49/1.49  fof(f63,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f30])).
% 7.49/1.49  
% 7.49/1.49  fof(f72,plain,(
% 7.49/1.49    ~v1_xboole_0(sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f73,plain,(
% 7.49/1.49    v1_funct_1(sK3)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f74,plain,(
% 7.49/1.49    v1_funct_2(sK3,sK1,sK0)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f76,plain,(
% 7.49/1.49    v1_funct_1(sK4)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f13,axiom,(
% 7.49/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f33,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f13])).
% 7.49/1.49  
% 7.49/1.49  fof(f34,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f33])).
% 7.49/1.49  
% 7.49/1.49  fof(f66,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f34])).
% 7.49/1.49  
% 7.49/1.49  fof(f8,axiom,(
% 7.49/1.49    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f23,plain,(
% 7.49/1.49    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f8])).
% 7.49/1.49  
% 7.49/1.49  fof(f24,plain,(
% 7.49/1.49    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f23])).
% 7.49/1.49  
% 7.49/1.49  fof(f58,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f24])).
% 7.49/1.49  
% 7.49/1.49  fof(f79,plain,(
% 7.49/1.49    v1_partfun1(sK4,sK0)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f71,plain,(
% 7.49/1.49    ~v1_xboole_0(sK0)),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f10,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f27,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f10])).
% 7.49/1.49  
% 7.49/1.49  fof(f28,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f27])).
% 7.49/1.49  
% 7.49/1.49  fof(f61,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f28])).
% 7.49/1.49  
% 7.49/1.49  fof(f5,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f20,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f5])).
% 7.49/1.49  
% 7.49/1.49  fof(f55,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f20])).
% 7.49/1.49  
% 7.49/1.49  fof(f3,axiom,(
% 7.49/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f19,plain,(
% 7.49/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.49/1.49    inference(ennf_transformation,[],[f3])).
% 7.49/1.49  
% 7.49/1.49  fof(f41,plain,(
% 7.49/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.49/1.49    inference(nnf_transformation,[],[f19])).
% 7.49/1.49  
% 7.49/1.49  fof(f51,plain,(
% 7.49/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f41])).
% 7.49/1.49  
% 7.49/1.49  fof(f2,axiom,(
% 7.49/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f18,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f2])).
% 7.49/1.49  
% 7.49/1.49  fof(f50,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f18])).
% 7.49/1.49  
% 7.49/1.49  fof(f4,axiom,(
% 7.49/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f53,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f4])).
% 7.49/1.49  
% 7.49/1.49  fof(f54,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f20])).
% 7.49/1.49  
% 7.49/1.49  fof(f9,axiom,(
% 7.49/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f25,plain,(
% 7.49/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.49/1.49    inference(ennf_transformation,[],[f9])).
% 7.49/1.49  
% 7.49/1.49  fof(f26,plain,(
% 7.49/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.49/1.49    inference(flattening,[],[f25])).
% 7.49/1.49  
% 7.49/1.49  fof(f42,plain,(
% 7.49/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.49/1.49    inference(nnf_transformation,[],[f26])).
% 7.49/1.49  
% 7.49/1.49  fof(f59,plain,(
% 7.49/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f42])).
% 7.49/1.49  
% 7.49/1.49  fof(f15,axiom,(
% 7.49/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f37,plain,(
% 7.49/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.49/1.49    inference(ennf_transformation,[],[f15])).
% 7.49/1.49  
% 7.49/1.49  fof(f38,plain,(
% 7.49/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.49/1.49    inference(flattening,[],[f37])).
% 7.49/1.49  
% 7.49/1.49  fof(f69,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f38])).
% 7.49/1.49  
% 7.49/1.49  fof(f80,plain,(
% 7.49/1.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 7.49/1.49    inference(cnf_transformation,[],[f48])).
% 7.49/1.49  
% 7.49/1.49  fof(f6,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f21,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f6])).
% 7.49/1.49  
% 7.49/1.49  fof(f56,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f21])).
% 7.49/1.49  
% 7.49/1.49  fof(f7,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f22,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f7])).
% 7.49/1.49  
% 7.49/1.49  fof(f57,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f22])).
% 7.49/1.49  
% 7.49/1.49  fof(f14,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f35,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.49/1.49    inference(ennf_transformation,[],[f14])).
% 7.49/1.49  
% 7.49/1.49  fof(f36,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.49/1.49    inference(flattening,[],[f35])).
% 7.49/1.49  
% 7.49/1.49  fof(f67,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f1,axiom,(
% 7.49/1.49    v1_xboole_0(k1_xboole_0)),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f49,plain,(
% 7.49/1.49    v1_xboole_0(k1_xboole_0)),
% 7.49/1.49    inference(cnf_transformation,[],[f1])).
% 7.49/1.49  
% 7.49/1.49  cnf(c_24,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK5,sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1317,plain,
% 7.49/1.49      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_25,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1316,plain,
% 7.49/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_27,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1314,plain,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1325,plain,
% 7.49/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.49/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 7.49/1.49      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 7.49/1.49      | v1_funct_1(X0) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X3,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1322,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 7.49/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3653,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.49/1.49      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.49/1.49      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 7.49/1.49      | m1_subset_1(X5,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top
% 7.49/1.49      | v1_funct_1(X4) != iProver_top
% 7.49/1.49      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1325,c_1322]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1323,plain,
% 7.49/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.49/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top
% 7.49/1.49      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X4)
% 7.49/1.49      | ~ v1_funct_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1324,plain,
% 7.49/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.49/1.49      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 7.49/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.49/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0) != iProver_top
% 7.49/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16977,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.49/1.49      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.49/1.49      | m1_subset_1(X5,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X4) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(forward_subsumption_resolution,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3653,c_1323,c_1324]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16985,plain,
% 7.49/1.49      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 7.49/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1314,c_16977]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_30,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_33,plain,
% 7.49/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_29,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_34,plain,
% 7.49/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_28,negated_conjecture,
% 7.49/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_35,plain,
% 7.49/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17209,plain,
% 7.49/1.49      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 7.49/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_16985,c_33,c_34,c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17221,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1316,c_17209]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_36,plain,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_26,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK4) ),
% 7.49/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_37,plain,
% 7.49/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_38,plain,
% 7.49/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1677,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_funct_1(k8_funct_2(X1,X2,X3,X0,sK4))
% 7.49/1.49      | ~ v1_funct_1(sK4) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1871,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | v1_funct_1(k8_funct_2(X0,X1,X2,sK3,sK4))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1677]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2368,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | v1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,sK4))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1871]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3421,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2368]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3422,plain,
% 7.49/1.49      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.49      | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) = iProver_top
% 7.49/1.49      | v1_funct_1(sK4) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3421]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1697,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | m1_subset_1(k8_funct_2(X1,X2,X3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(sK4) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1931,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.49/1.49      | m1_subset_1(k8_funct_2(X0,X1,X2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1697]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2378,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | m1_subset_1(k8_funct_2(sK1,sK0,X0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1931]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3454,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2378]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3455,plain,
% 7.49/1.49      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.49      | v1_funct_1(sK4) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3454]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1707,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,sK4),X1,X3)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | ~ v1_funct_1(sK4) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1951,plain,
% 7.49/1.49      ( v1_funct_2(k8_funct_2(X0,X1,X2,sK3,sK4),X0,X2)
% 7.49/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1707]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2409,plain,
% 7.49/1.49      ( v1_funct_2(k8_funct_2(sK1,sK0,X0,sK3,sK4),sK1,X0)
% 7.49/1.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1951]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3457,plain,
% 7.49/1.49      ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
% 7.49/1.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.49      | ~ v1_funct_1(sK4)
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2409]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3458,plain,
% 7.49/1.49      ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) = iProver_top
% 7.49/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.49      | v1_funct_1(sK4) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3457]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4310,plain,
% 7.49/1.49      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X2,X0)
% 7.49/1.49      | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
% 7.49/1.49      | v1_xboole_0(X0)
% 7.49/1.49      | k3_funct_2(X0,X1,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X2) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X2) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16946,plain,
% 7.49/1.49      ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
% 7.49/1.49      | ~ m1_subset_1(X0,sK1)
% 7.49/1.49      | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.49/1.49      | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
% 7.49/1.49      | v1_xboole_0(sK1)
% 7.49/1.49      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_4310]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16947,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 7.49/1.49      | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.49      | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.49/1.49      | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_16946]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17282,plain,
% 7.49/1.49      ( m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.49      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_17221,c_33,c_34,c_35,c_36,c_37,c_38,c_3422,c_3455,
% 7.49/1.49                 c_3458,c_16947]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17283,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_17282]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17291,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1317,c_17283]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X3,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1321,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
% 7.49/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2) != iProver_top
% 7.49/1.49      | v1_xboole_0(X1) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3652,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.49/1.49      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.49/1.49      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 7.49/1.49      | m1_subset_1(X5,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top
% 7.49/1.49      | v1_funct_1(X4) != iProver_top
% 7.49/1.49      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top
% 7.49/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1325,c_1321]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15963,plain,
% 7.49/1.49      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.49/1.49      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.49/1.49      | m1_subset_1(X5,X0) != iProver_top
% 7.49/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.49/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.49/1.49      | v1_funct_1(X4) != iProver_top
% 7.49/1.49      | v1_funct_1(X3) != iProver_top
% 7.49/1.49      | v1_xboole_0(X1) = iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(forward_subsumption_resolution,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3652,c_1323,c_1324]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15971,plain,
% 7.49/1.49      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 7.49/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top
% 7.49/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1314,c_15963]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16181,plain,
% 7.49/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.49/1.49      | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 7.49/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_15971,c_33,c_34,c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16182,plain,
% 7.49/1.49      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 7.49/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X1) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_16181]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16194,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK4) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1316,c_16182]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_9,plain,
% 7.49/1.49      ( ~ v1_partfun1(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_23,negated_conjecture,
% 7.49/1.49      ( v1_partfun1(sK4,sK0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_424,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_xboole_0(X2)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | sK4 != X0
% 7.49/1.49      | sK0 != X1 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_425,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.49      | ~ v1_xboole_0(X0)
% 7.49/1.49      | v1_xboole_0(sK0) ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_424]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_31,negated_conjecture,
% 7.49/1.49      ( ~ v1_xboole_0(sK0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_427,plain,
% 7.49/1.49      ( ~ v1_xboole_0(X0)
% 7.49/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_425,c_31]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_428,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.49      | ~ v1_xboole_0(X0) ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_427]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1307,plain,
% 7.49/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1994,plain,
% 7.49/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1316,c_1307]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16363,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_16194,c_37,c_1994]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16372,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1317,c_16363]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17329,plain,
% 7.49/1.49      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_17291,c_16372]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2572,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 7.49/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top
% 7.49/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1314,c_1322]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2689,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 7.49/1.49      | m1_subset_1(X0,sK1) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_2572,c_33,c_34,c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2697,plain,
% 7.49/1.49      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1317,c_2689]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.50      | ~ m1_subset_1(X3,X1)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | v1_xboole_0(X1) ),
% 7.49/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1326,plain,
% 7.49/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.49/1.50      | m1_subset_1(X3,X1) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 7.49/1.50      | v1_funct_1(X0) != iProver_top
% 7.49/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2796,plain,
% 7.49/1.50      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.50      | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 7.49/1.50      | m1_subset_1(sK5,sK1) != iProver_top
% 7.49/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK3) != iProver_top
% 7.49/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2697,c_1326]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_39,plain,
% 7.49/1.50      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3465,plain,
% 7.49/1.50      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2796,c_33,c_34,c_35,c_36,c_39]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5,plain,
% 7.49/1.50      ( v5_relat_1(X0,X1)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(X0),X1)
% 7.49/1.50      | ~ v5_relat_1(X0,X1)
% 7.49/1.50      | ~ v1_relat_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_332,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(X0),X1)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.49/1.50      | ~ v1_relat_1(X0) ),
% 7.49/1.50      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1309,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.49/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.49/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2777,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
% 7.49/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1309]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1,plain,
% 7.49/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.49/1.50      | ~ v1_relat_1(X1)
% 7.49/1.50      | v1_relat_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1572,plain,
% 7.49/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | v1_relat_1(X0)
% 7.49/1.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1762,plain,
% 7.49/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.49/1.50      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 7.49/1.50      | v1_relat_1(sK4) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1572]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1763,plain,
% 7.49/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.49/1.50      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 7.49/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1779,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1780,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3152,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2777,c_38,c_1763,c_1780]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1330,plain,
% 7.49/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.49/1.50      | v1_relat_1(X1) != iProver_top
% 7.49/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2392,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 7.49/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1330]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2640,plain,
% 7.49/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2392,c_38,c_1763,c_1780]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6,plain,
% 7.49/1.50      ( v4_relat_1(X0,X1)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11,plain,
% 7.49/1.50      ( ~ v1_partfun1(X0,X1)
% 7.49/1.50      | ~ v4_relat_1(X0,X1)
% 7.49/1.50      | ~ v1_relat_1(X0)
% 7.49/1.50      | k1_relat_1(X0) = X1 ),
% 7.49/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_411,plain,
% 7.49/1.50      ( ~ v4_relat_1(X0,X1)
% 7.49/1.50      | ~ v1_relat_1(X0)
% 7.49/1.50      | k1_relat_1(X0) = X1
% 7.49/1.50      | sK4 != X0
% 7.49/1.50      | sK0 != X1 ),
% 7.49/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_412,plain,
% 7.49/1.50      ( ~ v4_relat_1(sK4,sK0)
% 7.49/1.50      | ~ v1_relat_1(sK4)
% 7.49/1.50      | k1_relat_1(sK4) = sK0 ),
% 7.49/1.50      inference(unflattening,[status(thm)],[c_411]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_450,plain,
% 7.49/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ v1_relat_1(sK4)
% 7.49/1.50      | k1_relat_1(sK4) = sK0
% 7.49/1.50      | sK4 != X0
% 7.49/1.50      | sK0 != X1 ),
% 7.49/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_412]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_451,plain,
% 7.49/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.50      | ~ v1_relat_1(sK4)
% 7.49/1.50      | k1_relat_1(sK4) = sK0 ),
% 7.49/1.50      inference(unflattening,[status(thm)],[c_450]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_807,plain,
% 7.49/1.50      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 7.49/1.50      inference(splitting,
% 7.49/1.50                [splitting(split),new_symbols(definition,[])],
% 7.49/1.50                [c_451]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1305,plain,
% 7.49/1.50      ( k1_relat_1(sK4) = sK0
% 7.49/1.50      | v1_relat_1(sK4) != iProver_top
% 7.49/1.50      | sP0_iProver_split = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2645,plain,
% 7.49/1.50      ( k1_relat_1(sK4) = sK0 | sP0_iProver_split = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2640,c_1305]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_839,plain,
% 7.49/1.50      ( k1_relat_1(sK4) = sK0
% 7.49/1.50      | v1_relat_1(sK4) != iProver_top
% 7.49/1.50      | sP0_iProver_split = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_806,plain,
% 7.49/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 7.49/1.50      | ~ sP0_iProver_split ),
% 7.49/1.50      inference(splitting,
% 7.49/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.49/1.50                [c_451]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1306,plain,
% 7.49/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.50      | sP0_iProver_split != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2033,plain,
% 7.49/1.50      ( sP0_iProver_split != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1306]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2724,plain,
% 7.49/1.50      ( k1_relat_1(sK4) = sK0 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2645,c_38,c_839,c_1763,c_1780,c_2033]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20,plain,
% 7.49/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.49/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_relat_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1318,plain,
% 7.49/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.49/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.49/1.50      | v1_funct_1(X0) != iProver_top
% 7.49/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2729,plain,
% 7.49/1.50      ( v1_funct_2(sK4,sK0,X0) = iProver_top
% 7.49/1.50      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.49/1.50      | v1_funct_1(sK4) != iProver_top
% 7.49/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2724,c_1318]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3793,plain,
% 7.49/1.50      ( v1_funct_2(sK4,sK0,X0) = iProver_top
% 7.49/1.50      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2729,c_37,c_38,c_1763,c_1780]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3801,plain,
% 7.49/1.50      ( v1_funct_2(sK4,sK0,sK2) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3152,c_3793]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2963,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 7.49/1.50      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top
% 7.49/1.50      | v1_funct_1(sK4) != iProver_top
% 7.49/1.50      | v1_xboole_0(sK0) = iProver_top
% 7.49/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1321]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_32,plain,
% 7.49/1.50      ( v1_xboole_0(sK0) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3243,plain,
% 7.49/1.50      ( m1_subset_1(X0,sK0) != iProver_top
% 7.49/1.50      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 7.49/1.50      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2963,c_32,c_37,c_1994]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3244,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 7.49/1.50      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_3243]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3924,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3801,c_3244]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4515,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3465,c_3924]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2571,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 7.49/1.50      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top
% 7.49/1.50      | v1_funct_1(sK4) != iProver_top
% 7.49/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1322]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2654,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 7.49/1.50      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_2571,c_32,c_37]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3925,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 7.49/1.50      | m1_subset_1(X0,sK0) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3801,c_2654]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3944,plain,
% 7.49/1.50      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3465,c_3925]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4918,plain,
% 7.49/1.50      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_4515,c_3944]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_22,negated_conjecture,
% 7.49/1.50      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2699,plain,
% 7.49/1.50      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_2697,c_22]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4920,plain,
% 7.49/1.50      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_4918,c_2699]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16391,plain,
% 7.49/1.50      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_16372,c_4920]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_17333,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_17329,c_16391]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_811,plain,
% 7.49/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.49/1.50      theory(equality) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1577,plain,
% 7.49/1.50      ( v1_xboole_0(X0)
% 7.49/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.49/1.50      | X0 != k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_811]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16354,plain,
% 7.49/1.50      ( v1_xboole_0(sK1)
% 7.49/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.49/1.50      | sK1 != k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1577]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7,plain,
% 7.49/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1328,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.49/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2133,plain,
% 7.49/1.50      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1316,c_1328]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2727,plain,
% 7.49/1.50      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_2724,c_2133]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8,plain,
% 7.49/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1327,plain,
% 7.49/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.49/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1905,plain,
% 7.49/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1314,c_1327]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 7.49/1.50      | ~ m1_subset_1(X5,X1)
% 7.49/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ v1_funct_1(X4)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | v1_xboole_0(X2)
% 7.49/1.50      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k7_partfun1(X3,X4,k1_funct_1(X0,X5))
% 7.49/1.50      | k1_xboole_0 = X1 ),
% 7.49/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1320,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k7_partfun1(X2,X4,k1_funct_1(X3,X5))
% 7.49/1.50      | k1_xboole_0 = X0
% 7.49/1.50      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.49/1.50      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.49/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.49/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.50      | v1_funct_1(X3) != iProver_top
% 7.49/1.50      | v1_funct_1(X4) != iProver_top
% 7.49/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3534,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
% 7.49/1.50      | sK1 = k1_xboole_0
% 7.49/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.49/1.50      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
% 7.49/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.50      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.50      | v1_funct_1(X1) != iProver_top
% 7.49/1.50      | v1_funct_1(sK3) != iProver_top
% 7.49/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1905,c_1320]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4651,plain,
% 7.49/1.50      ( m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.50      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
% 7.49/1.50      | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
% 7.49/1.50      | sK1 = k1_xboole_0
% 7.49/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_3534,c_32,c_34,c_35,c_36]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4652,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,X1,k1_funct_1(sK3,X2))
% 7.49/1.50      | sK1 = k1_xboole_0
% 7.49/1.50      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) != iProver_top
% 7.49/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.49/1.50      | m1_subset_1(X2,sK1) != iProver_top
% 7.49/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_4651]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4663,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 7.49/1.50      | sK1 = k1_xboole_0
% 7.49/1.50      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
% 7.49/1.50      | m1_subset_1(X0,sK1) != iProver_top
% 7.49/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2727,c_4652]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1765,plain,
% 7.49/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.50      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.49/1.50      | v1_relat_1(sK3) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1572]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1766,plain,
% 7.49/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.50      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.49/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1782,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1783,plain,
% 7.49/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1782]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2778,plain,
% 7.49/1.50      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 7.49/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1314,c_1309]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5837,plain,
% 7.49/1.50      ( sK1 = k1_xboole_0
% 7.49/1.50      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 7.49/1.50      | m1_subset_1(X0,sK1) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_4663,c_36,c_37,c_38,c_1766,c_1783,c_2778]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5838,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 7.49/1.50      | sK1 = k1_xboole_0
% 7.49/1.50      | m1_subset_1(X0,sK1) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_5837]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5847,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
% 7.49/1.50      | sK1 = k1_xboole_0 ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1317,c_5838]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5850,plain,
% 7.49/1.50      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 7.49/1.50      | sK1 = k1_xboole_0 ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_5847,c_4918]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_0,plain,
% 7.49/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(contradiction,plain,
% 7.49/1.50      ( $false ),
% 7.49/1.50      inference(minisat,[status(thm)],[c_17333,c_16354,c_5850,c_0,c_30]) ).
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  ------                               Statistics
% 7.49/1.50  
% 7.49/1.50  ------ General
% 7.49/1.50  
% 7.49/1.50  abstr_ref_over_cycles:                  0
% 7.49/1.50  abstr_ref_under_cycles:                 0
% 7.49/1.50  gc_basic_clause_elim:                   0
% 7.49/1.50  forced_gc_time:                         0
% 7.49/1.50  parsing_time:                           0.012
% 7.49/1.50  unif_index_cands_time:                  0.
% 7.49/1.50  unif_index_add_time:                    0.
% 7.49/1.50  orderings_time:                         0.
% 7.49/1.50  out_proof_time:                         0.017
% 7.49/1.50  total_time:                             0.672
% 7.49/1.50  num_of_symbols:                         58
% 7.49/1.50  num_of_terms:                           24267
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing
% 7.49/1.50  
% 7.49/1.50  num_of_splits:                          1
% 7.49/1.50  num_of_split_atoms:                     1
% 7.49/1.50  num_of_reused_defs:                     0
% 7.49/1.50  num_eq_ax_congr_red:                    28
% 7.49/1.50  num_of_sem_filtered_clauses:            1
% 7.49/1.50  num_of_subtypes:                        0
% 7.49/1.50  monotx_restored_types:                  0
% 7.49/1.50  sat_num_of_epr_types:                   0
% 7.49/1.50  sat_num_of_non_cyclic_types:            0
% 7.49/1.50  sat_guarded_non_collapsed_types:        0
% 7.49/1.50  num_pure_diseq_elim:                    0
% 7.49/1.50  simp_replaced_by:                       0
% 7.49/1.50  res_preprocessed:                       145
% 7.49/1.50  prep_upred:                             0
% 7.49/1.50  prep_unflattend:                        14
% 7.49/1.50  smt_new_axioms:                         0
% 7.49/1.50  pred_elim_cands:                        6
% 7.49/1.50  pred_elim:                              3
% 7.49/1.50  pred_elim_cl:                           4
% 7.49/1.50  pred_elim_cycles:                       6
% 7.49/1.50  merged_defs:                            0
% 7.49/1.50  merged_defs_ncl:                        0
% 7.49/1.50  bin_hyper_res:                          0
% 7.49/1.50  prep_cycles:                            4
% 7.49/1.50  pred_elim_time:                         0.007
% 7.49/1.50  splitting_time:                         0.
% 7.49/1.50  sem_filter_time:                        0.
% 7.49/1.50  monotx_time:                            0.001
% 7.49/1.50  subtype_inf_time:                       0.
% 7.49/1.50  
% 7.49/1.50  ------ Problem properties
% 7.49/1.50  
% 7.49/1.50  clauses:                                28
% 7.49/1.50  conjectures:                            9
% 7.49/1.50  epr:                                    7
% 7.49/1.50  horn:                                   23
% 7.49/1.50  ground:                                 11
% 7.49/1.50  unary:                                  11
% 7.49/1.50  binary:                                 4
% 7.49/1.50  lits:                                   87
% 7.49/1.50  lits_eq:                                8
% 7.49/1.50  fd_pure:                                0
% 7.49/1.50  fd_pseudo:                              0
% 7.49/1.50  fd_cond:                                1
% 7.49/1.50  fd_pseudo_cond:                         0
% 7.49/1.50  ac_symbols:                             0
% 7.49/1.50  
% 7.49/1.50  ------ Propositional Solver
% 7.49/1.50  
% 7.49/1.50  prop_solver_calls:                      31
% 7.49/1.50  prop_fast_solver_calls:                 2453
% 7.49/1.50  smt_solver_calls:                       0
% 7.49/1.50  smt_fast_solver_calls:                  0
% 7.49/1.50  prop_num_of_clauses:                    7131
% 7.49/1.50  prop_preprocess_simplified:             11361
% 7.49/1.50  prop_fo_subsumed:                       160
% 7.49/1.50  prop_solver_time:                       0.
% 7.49/1.50  smt_solver_time:                        0.
% 7.49/1.50  smt_fast_solver_time:                   0.
% 7.49/1.50  prop_fast_solver_time:                  0.
% 7.49/1.50  prop_unsat_core_time:                   0.
% 7.49/1.50  
% 7.49/1.50  ------ QBF
% 7.49/1.50  
% 7.49/1.50  qbf_q_res:                              0
% 7.49/1.50  qbf_num_tautologies:                    0
% 7.49/1.50  qbf_prep_cycles:                        0
% 7.49/1.50  
% 7.49/1.50  ------ BMC1
% 7.49/1.50  
% 7.49/1.50  bmc1_current_bound:                     -1
% 7.49/1.50  bmc1_last_solved_bound:                 -1
% 7.49/1.50  bmc1_unsat_core_size:                   -1
% 7.49/1.50  bmc1_unsat_core_parents_size:           -1
% 7.49/1.50  bmc1_merge_next_fun:                    0
% 7.49/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation
% 7.49/1.50  
% 7.49/1.50  inst_num_of_clauses:                    1532
% 7.49/1.50  inst_num_in_passive:                    248
% 7.49/1.50  inst_num_in_active:                     913
% 7.49/1.50  inst_num_in_unprocessed:                371
% 7.49/1.50  inst_num_of_loops:                      980
% 7.49/1.50  inst_num_of_learning_restarts:          0
% 7.49/1.50  inst_num_moves_active_passive:          62
% 7.49/1.50  inst_lit_activity:                      0
% 7.49/1.50  inst_lit_activity_moves:                1
% 7.49/1.50  inst_num_tautologies:                   0
% 7.49/1.50  inst_num_prop_implied:                  0
% 7.49/1.50  inst_num_existing_simplified:           0
% 7.49/1.50  inst_num_eq_res_simplified:             0
% 7.49/1.50  inst_num_child_elim:                    0
% 7.49/1.50  inst_num_of_dismatching_blockings:      96
% 7.49/1.50  inst_num_of_non_proper_insts:           1084
% 7.49/1.50  inst_num_of_duplicates:                 0
% 7.49/1.50  inst_inst_num_from_inst_to_res:         0
% 7.49/1.50  inst_dismatching_checking_time:         0.
% 7.49/1.50  
% 7.49/1.50  ------ Resolution
% 7.49/1.50  
% 7.49/1.50  res_num_of_clauses:                     0
% 7.49/1.50  res_num_in_passive:                     0
% 7.49/1.50  res_num_in_active:                      0
% 7.49/1.50  res_num_of_loops:                       149
% 7.49/1.50  res_forward_subset_subsumed:            67
% 7.49/1.50  res_backward_subset_subsumed:           0
% 7.49/1.50  res_forward_subsumed:                   0
% 7.49/1.50  res_backward_subsumed:                  0
% 7.49/1.50  res_forward_subsumption_resolution:     1
% 7.49/1.50  res_backward_subsumption_resolution:    0
% 7.49/1.50  res_clause_to_clause_subsumption:       3371
% 7.49/1.50  res_orphan_elimination:                 0
% 7.49/1.50  res_tautology_del:                      95
% 7.49/1.50  res_num_eq_res_simplified:              0
% 7.49/1.50  res_num_sel_changes:                    0
% 7.49/1.50  res_moves_from_active_to_pass:          0
% 7.49/1.50  
% 7.49/1.50  ------ Superposition
% 7.49/1.50  
% 7.49/1.50  sup_time_total:                         0.
% 7.49/1.50  sup_time_generating:                    0.
% 7.49/1.50  sup_time_sim_full:                      0.
% 7.49/1.50  sup_time_sim_immed:                     0.
% 7.49/1.50  
% 7.49/1.50  sup_num_of_clauses:                     405
% 7.49/1.50  sup_num_in_active:                      188
% 7.49/1.50  sup_num_in_passive:                     217
% 7.49/1.50  sup_num_of_loops:                       195
% 7.49/1.50  sup_fw_superposition:                   350
% 7.49/1.50  sup_bw_superposition:                   52
% 7.49/1.50  sup_immediate_simplified:               23
% 7.49/1.50  sup_given_eliminated:                   0
% 7.49/1.50  comparisons_done:                       0
% 7.49/1.50  comparisons_avoided:                    15
% 7.49/1.50  
% 7.49/1.50  ------ Simplifications
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  sim_fw_subset_subsumed:                 6
% 7.49/1.50  sim_bw_subset_subsumed:                 1
% 7.49/1.50  sim_fw_subsumed:                        4
% 7.49/1.50  sim_bw_subsumed:                        0
% 7.49/1.50  sim_fw_subsumption_res:                 61
% 7.49/1.50  sim_bw_subsumption_res:                 0
% 7.49/1.50  sim_tautology_del:                      3
% 7.49/1.50  sim_eq_tautology_del:                   4
% 7.49/1.50  sim_eq_res_simp:                        0
% 7.49/1.50  sim_fw_demodulated:                     0
% 7.49/1.50  sim_bw_demodulated:                     6
% 7.49/1.50  sim_light_normalised:                   16
% 7.49/1.50  sim_joinable_taut:                      0
% 7.49/1.50  sim_joinable_simp:                      0
% 7.49/1.50  sim_ac_normalised:                      0
% 7.49/1.50  sim_smt_subsumption:                    0
% 7.49/1.50  
%------------------------------------------------------------------------------
