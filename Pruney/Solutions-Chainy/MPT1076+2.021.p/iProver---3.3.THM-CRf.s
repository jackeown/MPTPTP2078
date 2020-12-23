%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:24 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 770 expanded)
%              Number of clauses        :   69 ( 150 expanded)
%              Number of leaves         :   12 ( 324 expanded)
%              Depth                    :   20
%              Number of atoms          :  520 (6995 expanded)
%              Number of equality atoms :  105 ( 934 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f29,f28,f27,f26,f25])).

fof(f47,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_951,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_17,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_17,c_16,c_14])).

cnf(c_948,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_1128,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_951,c_948])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_17,c_16,c_14])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_946,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1187,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1128,c_946])).

cnf(c_26,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1313,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_26])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_950,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_170,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_171,plain,
    ( v1_funct_2(sK4,sK0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_175,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | v1_funct_2(sK4,sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171,c_13])).

cnf(c_176,plain,
    ( v1_funct_2(sK4,sK0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 != X3
    | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
    | sK4 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_176])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK0)
    | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_553,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_18,c_13])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | v1_xboole_0(X1)
    | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_189,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_191,plain,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_18])).

cnf(c_192,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_554,c_192])).

cnf(c_944,plain,
    ( k3_funct_2(sK0,X0,sK4,X1) = k7_partfun1(X0,sK4,X1)
    | m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_1706,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_944])).

cnf(c_1794,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1313,c_1706])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | X4 != X3
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK4 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_176])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | k3_funct_2(sK0,X1,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK0,X1,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_18,c_13])).

cnf(c_945,plain,
    ( k3_funct_2(sK0,X0,sK4,X1) = k1_funct_1(sK4,X1)
    | m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1647,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_945])).

cnf(c_1715,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1313,c_1647])).

cnf(c_1838,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1794,c_1715])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X4,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k3_funct_2(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_202,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k3_funct_2(X1,X2,X0,X3))
    | sK4 != X4
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_203,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK0)
    | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_207,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_2(X0,X1,sK0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_18,c_13])).

cnf(c_208,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0))
    | sK3 != X2
    | sK0 != sK0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_208])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_17,c_16,c_14])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_942,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1))
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1394,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_942])).

cnf(c_1466,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_951,c_1394])).

cnf(c_1467,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1466,c_1128])).

cnf(c_9,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1186,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1128,c_9])).

cnf(c_1542,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1467,c_1186])).

cnf(c_1840,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1838,c_1542])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.06/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.06/1.03  
% 1.06/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.06/1.03  
% 1.06/1.03  ------  iProver source info
% 1.06/1.03  
% 1.06/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.06/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.06/1.03  git: non_committed_changes: false
% 1.06/1.03  git: last_make_outside_of_git: false
% 1.06/1.03  
% 1.06/1.03  ------ 
% 1.06/1.03  
% 1.06/1.03  ------ Input Options
% 1.06/1.03  
% 1.06/1.03  --out_options                           all
% 1.06/1.03  --tptp_safe_out                         true
% 1.06/1.03  --problem_path                          ""
% 1.06/1.03  --include_path                          ""
% 1.06/1.03  --clausifier                            res/vclausify_rel
% 1.06/1.03  --clausifier_options                    --mode clausify
% 1.06/1.03  --stdin                                 false
% 1.06/1.03  --stats_out                             all
% 1.06/1.03  
% 1.06/1.03  ------ General Options
% 1.06/1.03  
% 1.06/1.03  --fof                                   false
% 1.06/1.03  --time_out_real                         305.
% 1.06/1.03  --time_out_virtual                      -1.
% 1.06/1.03  --symbol_type_check                     false
% 1.06/1.03  --clausify_out                          false
% 1.06/1.03  --sig_cnt_out                           false
% 1.06/1.03  --trig_cnt_out                          false
% 1.06/1.03  --trig_cnt_out_tolerance                1.
% 1.06/1.03  --trig_cnt_out_sk_spl                   false
% 1.06/1.03  --abstr_cl_out                          false
% 1.06/1.03  
% 1.06/1.03  ------ Global Options
% 1.06/1.03  
% 1.06/1.03  --schedule                              default
% 1.06/1.03  --add_important_lit                     false
% 1.06/1.03  --prop_solver_per_cl                    1000
% 1.06/1.03  --min_unsat_core                        false
% 1.06/1.03  --soft_assumptions                      false
% 1.06/1.03  --soft_lemma_size                       3
% 1.06/1.03  --prop_impl_unit_size                   0
% 1.06/1.03  --prop_impl_unit                        []
% 1.06/1.03  --share_sel_clauses                     true
% 1.06/1.03  --reset_solvers                         false
% 1.06/1.03  --bc_imp_inh                            [conj_cone]
% 1.06/1.03  --conj_cone_tolerance                   3.
% 1.06/1.03  --extra_neg_conj                        none
% 1.06/1.03  --large_theory_mode                     true
% 1.06/1.03  --prolific_symb_bound                   200
% 1.06/1.03  --lt_threshold                          2000
% 1.06/1.03  --clause_weak_htbl                      true
% 1.06/1.03  --gc_record_bc_elim                     false
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing Options
% 1.06/1.03  
% 1.06/1.03  --preprocessing_flag                    true
% 1.06/1.03  --time_out_prep_mult                    0.1
% 1.06/1.03  --splitting_mode                        input
% 1.06/1.03  --splitting_grd                         true
% 1.06/1.03  --splitting_cvd                         false
% 1.06/1.03  --splitting_cvd_svl                     false
% 1.06/1.03  --splitting_nvd                         32
% 1.06/1.03  --sub_typing                            true
% 1.06/1.03  --prep_gs_sim                           true
% 1.06/1.03  --prep_unflatten                        true
% 1.06/1.03  --prep_res_sim                          true
% 1.06/1.03  --prep_upred                            true
% 1.06/1.03  --prep_sem_filter                       exhaustive
% 1.06/1.03  --prep_sem_filter_out                   false
% 1.06/1.03  --pred_elim                             true
% 1.06/1.03  --res_sim_input                         true
% 1.06/1.03  --eq_ax_congr_red                       true
% 1.06/1.03  --pure_diseq_elim                       true
% 1.06/1.03  --brand_transform                       false
% 1.06/1.03  --non_eq_to_eq                          false
% 1.06/1.03  --prep_def_merge                        true
% 1.06/1.03  --prep_def_merge_prop_impl              false
% 1.06/1.03  --prep_def_merge_mbd                    true
% 1.06/1.03  --prep_def_merge_tr_red                 false
% 1.06/1.03  --prep_def_merge_tr_cl                  false
% 1.06/1.03  --smt_preprocessing                     true
% 1.06/1.03  --smt_ac_axioms                         fast
% 1.06/1.03  --preprocessed_out                      false
% 1.06/1.03  --preprocessed_stats                    false
% 1.06/1.03  
% 1.06/1.03  ------ Abstraction refinement Options
% 1.06/1.03  
% 1.06/1.03  --abstr_ref                             []
% 1.06/1.03  --abstr_ref_prep                        false
% 1.06/1.03  --abstr_ref_until_sat                   false
% 1.06/1.03  --abstr_ref_sig_restrict                funpre
% 1.06/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.06/1.03  --abstr_ref_under                       []
% 1.06/1.03  
% 1.06/1.03  ------ SAT Options
% 1.06/1.03  
% 1.06/1.03  --sat_mode                              false
% 1.06/1.03  --sat_fm_restart_options                ""
% 1.06/1.03  --sat_gr_def                            false
% 1.06/1.03  --sat_epr_types                         true
% 1.06/1.03  --sat_non_cyclic_types                  false
% 1.06/1.03  --sat_finite_models                     false
% 1.06/1.03  --sat_fm_lemmas                         false
% 1.06/1.03  --sat_fm_prep                           false
% 1.06/1.03  --sat_fm_uc_incr                        true
% 1.06/1.03  --sat_out_model                         small
% 1.06/1.03  --sat_out_clauses                       false
% 1.06/1.03  
% 1.06/1.03  ------ QBF Options
% 1.06/1.03  
% 1.06/1.03  --qbf_mode                              false
% 1.06/1.03  --qbf_elim_univ                         false
% 1.06/1.03  --qbf_dom_inst                          none
% 1.06/1.03  --qbf_dom_pre_inst                      false
% 1.06/1.03  --qbf_sk_in                             false
% 1.06/1.03  --qbf_pred_elim                         true
% 1.06/1.03  --qbf_split                             512
% 1.06/1.03  
% 1.06/1.03  ------ BMC1 Options
% 1.06/1.03  
% 1.06/1.03  --bmc1_incremental                      false
% 1.06/1.03  --bmc1_axioms                           reachable_all
% 1.06/1.03  --bmc1_min_bound                        0
% 1.06/1.03  --bmc1_max_bound                        -1
% 1.06/1.03  --bmc1_max_bound_default                -1
% 1.06/1.03  --bmc1_symbol_reachability              true
% 1.06/1.03  --bmc1_property_lemmas                  false
% 1.06/1.03  --bmc1_k_induction                      false
% 1.06/1.03  --bmc1_non_equiv_states                 false
% 1.06/1.03  --bmc1_deadlock                         false
% 1.06/1.03  --bmc1_ucm                              false
% 1.06/1.03  --bmc1_add_unsat_core                   none
% 1.06/1.03  --bmc1_unsat_core_children              false
% 1.06/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.06/1.03  --bmc1_out_stat                         full
% 1.06/1.03  --bmc1_ground_init                      false
% 1.06/1.03  --bmc1_pre_inst_next_state              false
% 1.06/1.03  --bmc1_pre_inst_state                   false
% 1.06/1.03  --bmc1_pre_inst_reach_state             false
% 1.06/1.03  --bmc1_out_unsat_core                   false
% 1.06/1.03  --bmc1_aig_witness_out                  false
% 1.06/1.03  --bmc1_verbose                          false
% 1.06/1.03  --bmc1_dump_clauses_tptp                false
% 1.06/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.06/1.03  --bmc1_dump_file                        -
% 1.06/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.06/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.06/1.03  --bmc1_ucm_extend_mode                  1
% 1.06/1.03  --bmc1_ucm_init_mode                    2
% 1.06/1.03  --bmc1_ucm_cone_mode                    none
% 1.06/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.06/1.03  --bmc1_ucm_relax_model                  4
% 1.06/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.06/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.06/1.03  --bmc1_ucm_layered_model                none
% 1.06/1.03  --bmc1_ucm_max_lemma_size               10
% 1.06/1.03  
% 1.06/1.03  ------ AIG Options
% 1.06/1.03  
% 1.06/1.03  --aig_mode                              false
% 1.06/1.03  
% 1.06/1.03  ------ Instantiation Options
% 1.06/1.03  
% 1.06/1.03  --instantiation_flag                    true
% 1.06/1.03  --inst_sos_flag                         false
% 1.06/1.03  --inst_sos_phase                        true
% 1.06/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.06/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.06/1.03  --inst_lit_sel_side                     num_symb
% 1.06/1.03  --inst_solver_per_active                1400
% 1.06/1.03  --inst_solver_calls_frac                1.
% 1.06/1.03  --inst_passive_queue_type               priority_queues
% 1.06/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.06/1.03  --inst_passive_queues_freq              [25;2]
% 1.06/1.03  --inst_dismatching                      true
% 1.06/1.03  --inst_eager_unprocessed_to_passive     true
% 1.06/1.03  --inst_prop_sim_given                   true
% 1.06/1.03  --inst_prop_sim_new                     false
% 1.06/1.03  --inst_subs_new                         false
% 1.06/1.03  --inst_eq_res_simp                      false
% 1.06/1.03  --inst_subs_given                       false
% 1.06/1.03  --inst_orphan_elimination               true
% 1.06/1.03  --inst_learning_loop_flag               true
% 1.06/1.03  --inst_learning_start                   3000
% 1.06/1.03  --inst_learning_factor                  2
% 1.06/1.03  --inst_start_prop_sim_after_learn       3
% 1.06/1.03  --inst_sel_renew                        solver
% 1.06/1.03  --inst_lit_activity_flag                true
% 1.06/1.03  --inst_restr_to_given                   false
% 1.06/1.03  --inst_activity_threshold               500
% 1.06/1.03  --inst_out_proof                        true
% 1.06/1.03  
% 1.06/1.03  ------ Resolution Options
% 1.06/1.03  
% 1.06/1.03  --resolution_flag                       true
% 1.06/1.03  --res_lit_sel                           adaptive
% 1.06/1.03  --res_lit_sel_side                      none
% 1.06/1.03  --res_ordering                          kbo
% 1.06/1.03  --res_to_prop_solver                    active
% 1.06/1.03  --res_prop_simpl_new                    false
% 1.06/1.03  --res_prop_simpl_given                  true
% 1.06/1.03  --res_passive_queue_type                priority_queues
% 1.06/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.06/1.03  --res_passive_queues_freq               [15;5]
% 1.06/1.03  --res_forward_subs                      full
% 1.06/1.03  --res_backward_subs                     full
% 1.06/1.03  --res_forward_subs_resolution           true
% 1.06/1.03  --res_backward_subs_resolution          true
% 1.06/1.03  --res_orphan_elimination                true
% 1.06/1.03  --res_time_limit                        2.
% 1.06/1.03  --res_out_proof                         true
% 1.06/1.03  
% 1.06/1.03  ------ Superposition Options
% 1.06/1.03  
% 1.06/1.03  --superposition_flag                    true
% 1.06/1.03  --sup_passive_queue_type                priority_queues
% 1.06/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.06/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.06/1.03  --demod_completeness_check              fast
% 1.06/1.03  --demod_use_ground                      true
% 1.06/1.03  --sup_to_prop_solver                    passive
% 1.06/1.03  --sup_prop_simpl_new                    true
% 1.06/1.03  --sup_prop_simpl_given                  true
% 1.06/1.03  --sup_fun_splitting                     false
% 1.06/1.03  --sup_smt_interval                      50000
% 1.06/1.03  
% 1.06/1.03  ------ Superposition Simplification Setup
% 1.06/1.03  
% 1.06/1.03  --sup_indices_passive                   []
% 1.06/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.06/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.03  --sup_full_bw                           [BwDemod]
% 1.06/1.03  --sup_immed_triv                        [TrivRules]
% 1.06/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.06/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.03  --sup_immed_bw_main                     []
% 1.06/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.06/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.03  
% 1.06/1.03  ------ Combination Options
% 1.06/1.03  
% 1.06/1.03  --comb_res_mult                         3
% 1.06/1.03  --comb_sup_mult                         2
% 1.06/1.03  --comb_inst_mult                        10
% 1.06/1.03  
% 1.06/1.03  ------ Debug Options
% 1.06/1.03  
% 1.06/1.03  --dbg_backtrace                         false
% 1.06/1.03  --dbg_dump_prop_clauses                 false
% 1.06/1.03  --dbg_dump_prop_clauses_file            -
% 1.06/1.03  --dbg_out_stat                          false
% 1.06/1.03  ------ Parsing...
% 1.06/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.06/1.03  ------ Proving...
% 1.06/1.03  ------ Problem Properties 
% 1.06/1.03  
% 1.06/1.03  
% 1.06/1.03  clauses                                 13
% 1.06/1.03  conjectures                             4
% 1.06/1.03  EPR                                     1
% 1.06/1.03  Horn                                    13
% 1.06/1.03  unary                                   4
% 1.06/1.03  binary                                  4
% 1.06/1.03  lits                                    28
% 1.06/1.03  lits eq                                 9
% 1.06/1.03  fd_pure                                 0
% 1.06/1.03  fd_pseudo                               0
% 1.06/1.03  fd_cond                                 0
% 1.06/1.03  fd_pseudo_cond                          1
% 1.06/1.03  AC symbols                              0
% 1.06/1.03  
% 1.06/1.03  ------ Schedule dynamic 5 is on 
% 1.06/1.03  
% 1.06/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.06/1.03  
% 1.06/1.03  
% 1.06/1.03  ------ 
% 1.06/1.03  Current options:
% 1.06/1.03  ------ 
% 1.06/1.03  
% 1.06/1.03  ------ Input Options
% 1.06/1.03  
% 1.06/1.03  --out_options                           all
% 1.06/1.03  --tptp_safe_out                         true
% 1.06/1.03  --problem_path                          ""
% 1.06/1.03  --include_path                          ""
% 1.06/1.03  --clausifier                            res/vclausify_rel
% 1.06/1.03  --clausifier_options                    --mode clausify
% 1.06/1.03  --stdin                                 false
% 1.06/1.03  --stats_out                             all
% 1.06/1.03  
% 1.06/1.03  ------ General Options
% 1.06/1.03  
% 1.06/1.03  --fof                                   false
% 1.06/1.03  --time_out_real                         305.
% 1.06/1.03  --time_out_virtual                      -1.
% 1.06/1.03  --symbol_type_check                     false
% 1.06/1.03  --clausify_out                          false
% 1.06/1.03  --sig_cnt_out                           false
% 1.06/1.03  --trig_cnt_out                          false
% 1.06/1.03  --trig_cnt_out_tolerance                1.
% 1.06/1.03  --trig_cnt_out_sk_spl                   false
% 1.06/1.03  --abstr_cl_out                          false
% 1.06/1.03  
% 1.06/1.03  ------ Global Options
% 1.06/1.03  
% 1.06/1.03  --schedule                              default
% 1.06/1.03  --add_important_lit                     false
% 1.06/1.03  --prop_solver_per_cl                    1000
% 1.06/1.03  --min_unsat_core                        false
% 1.06/1.03  --soft_assumptions                      false
% 1.06/1.03  --soft_lemma_size                       3
% 1.06/1.03  --prop_impl_unit_size                   0
% 1.06/1.03  --prop_impl_unit                        []
% 1.06/1.03  --share_sel_clauses                     true
% 1.06/1.03  --reset_solvers                         false
% 1.06/1.03  --bc_imp_inh                            [conj_cone]
% 1.06/1.03  --conj_cone_tolerance                   3.
% 1.06/1.03  --extra_neg_conj                        none
% 1.06/1.03  --large_theory_mode                     true
% 1.06/1.03  --prolific_symb_bound                   200
% 1.06/1.03  --lt_threshold                          2000
% 1.06/1.03  --clause_weak_htbl                      true
% 1.06/1.03  --gc_record_bc_elim                     false
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing Options
% 1.06/1.03  
% 1.06/1.03  --preprocessing_flag                    true
% 1.06/1.03  --time_out_prep_mult                    0.1
% 1.06/1.03  --splitting_mode                        input
% 1.06/1.03  --splitting_grd                         true
% 1.06/1.03  --splitting_cvd                         false
% 1.06/1.03  --splitting_cvd_svl                     false
% 1.06/1.03  --splitting_nvd                         32
% 1.06/1.03  --sub_typing                            true
% 1.06/1.03  --prep_gs_sim                           true
% 1.06/1.03  --prep_unflatten                        true
% 1.06/1.03  --prep_res_sim                          true
% 1.06/1.03  --prep_upred                            true
% 1.06/1.03  --prep_sem_filter                       exhaustive
% 1.06/1.03  --prep_sem_filter_out                   false
% 1.06/1.03  --pred_elim                             true
% 1.06/1.03  --res_sim_input                         true
% 1.06/1.03  --eq_ax_congr_red                       true
% 1.06/1.03  --pure_diseq_elim                       true
% 1.06/1.03  --brand_transform                       false
% 1.06/1.03  --non_eq_to_eq                          false
% 1.06/1.03  --prep_def_merge                        true
% 1.06/1.03  --prep_def_merge_prop_impl              false
% 1.06/1.03  --prep_def_merge_mbd                    true
% 1.06/1.03  --prep_def_merge_tr_red                 false
% 1.06/1.03  --prep_def_merge_tr_cl                  false
% 1.06/1.03  --smt_preprocessing                     true
% 1.06/1.03  --smt_ac_axioms                         fast
% 1.06/1.03  --preprocessed_out                      false
% 1.06/1.03  --preprocessed_stats                    false
% 1.06/1.03  
% 1.06/1.03  ------ Abstraction refinement Options
% 1.06/1.03  
% 1.06/1.03  --abstr_ref                             []
% 1.06/1.03  --abstr_ref_prep                        false
% 1.06/1.03  --abstr_ref_until_sat                   false
% 1.06/1.03  --abstr_ref_sig_restrict                funpre
% 1.06/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.06/1.03  --abstr_ref_under                       []
% 1.06/1.03  
% 1.06/1.03  ------ SAT Options
% 1.06/1.03  
% 1.06/1.03  --sat_mode                              false
% 1.06/1.03  --sat_fm_restart_options                ""
% 1.06/1.03  --sat_gr_def                            false
% 1.06/1.03  --sat_epr_types                         true
% 1.06/1.03  --sat_non_cyclic_types                  false
% 1.06/1.03  --sat_finite_models                     false
% 1.06/1.03  --sat_fm_lemmas                         false
% 1.06/1.03  --sat_fm_prep                           false
% 1.06/1.03  --sat_fm_uc_incr                        true
% 1.06/1.03  --sat_out_model                         small
% 1.06/1.03  --sat_out_clauses                       false
% 1.06/1.03  
% 1.06/1.03  ------ QBF Options
% 1.06/1.03  
% 1.06/1.03  --qbf_mode                              false
% 1.06/1.03  --qbf_elim_univ                         false
% 1.06/1.03  --qbf_dom_inst                          none
% 1.06/1.03  --qbf_dom_pre_inst                      false
% 1.06/1.03  --qbf_sk_in                             false
% 1.06/1.03  --qbf_pred_elim                         true
% 1.06/1.03  --qbf_split                             512
% 1.06/1.03  
% 1.06/1.03  ------ BMC1 Options
% 1.06/1.03  
% 1.06/1.03  --bmc1_incremental                      false
% 1.06/1.03  --bmc1_axioms                           reachable_all
% 1.06/1.03  --bmc1_min_bound                        0
% 1.06/1.03  --bmc1_max_bound                        -1
% 1.06/1.03  --bmc1_max_bound_default                -1
% 1.06/1.03  --bmc1_symbol_reachability              true
% 1.06/1.03  --bmc1_property_lemmas                  false
% 1.06/1.03  --bmc1_k_induction                      false
% 1.06/1.03  --bmc1_non_equiv_states                 false
% 1.06/1.03  --bmc1_deadlock                         false
% 1.06/1.03  --bmc1_ucm                              false
% 1.06/1.03  --bmc1_add_unsat_core                   none
% 1.06/1.03  --bmc1_unsat_core_children              false
% 1.06/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.06/1.03  --bmc1_out_stat                         full
% 1.06/1.03  --bmc1_ground_init                      false
% 1.06/1.03  --bmc1_pre_inst_next_state              false
% 1.06/1.03  --bmc1_pre_inst_state                   false
% 1.06/1.03  --bmc1_pre_inst_reach_state             false
% 1.06/1.03  --bmc1_out_unsat_core                   false
% 1.06/1.03  --bmc1_aig_witness_out                  false
% 1.06/1.03  --bmc1_verbose                          false
% 1.06/1.03  --bmc1_dump_clauses_tptp                false
% 1.06/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.06/1.03  --bmc1_dump_file                        -
% 1.06/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.06/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.06/1.03  --bmc1_ucm_extend_mode                  1
% 1.06/1.03  --bmc1_ucm_init_mode                    2
% 1.06/1.03  --bmc1_ucm_cone_mode                    none
% 1.06/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.06/1.03  --bmc1_ucm_relax_model                  4
% 1.06/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.06/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.06/1.03  --bmc1_ucm_layered_model                none
% 1.06/1.03  --bmc1_ucm_max_lemma_size               10
% 1.06/1.03  
% 1.06/1.03  ------ AIG Options
% 1.06/1.03  
% 1.06/1.03  --aig_mode                              false
% 1.06/1.03  
% 1.06/1.03  ------ Instantiation Options
% 1.06/1.03  
% 1.06/1.03  --instantiation_flag                    true
% 1.06/1.03  --inst_sos_flag                         false
% 1.06/1.03  --inst_sos_phase                        true
% 1.06/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.06/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.06/1.03  --inst_lit_sel_side                     none
% 1.06/1.03  --inst_solver_per_active                1400
% 1.06/1.03  --inst_solver_calls_frac                1.
% 1.06/1.03  --inst_passive_queue_type               priority_queues
% 1.06/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.06/1.04  --inst_passive_queues_freq              [25;2]
% 1.06/1.04  --inst_dismatching                      true
% 1.06/1.04  --inst_eager_unprocessed_to_passive     true
% 1.06/1.04  --inst_prop_sim_given                   true
% 1.06/1.04  --inst_prop_sim_new                     false
% 1.06/1.04  --inst_subs_new                         false
% 1.06/1.04  --inst_eq_res_simp                      false
% 1.06/1.04  --inst_subs_given                       false
% 1.06/1.04  --inst_orphan_elimination               true
% 1.06/1.04  --inst_learning_loop_flag               true
% 1.06/1.04  --inst_learning_start                   3000
% 1.06/1.04  --inst_learning_factor                  2
% 1.06/1.04  --inst_start_prop_sim_after_learn       3
% 1.06/1.04  --inst_sel_renew                        solver
% 1.06/1.04  --inst_lit_activity_flag                true
% 1.06/1.04  --inst_restr_to_given                   false
% 1.06/1.04  --inst_activity_threshold               500
% 1.06/1.04  --inst_out_proof                        true
% 1.06/1.04  
% 1.06/1.04  ------ Resolution Options
% 1.06/1.04  
% 1.06/1.04  --resolution_flag                       false
% 1.06/1.04  --res_lit_sel                           adaptive
% 1.06/1.04  --res_lit_sel_side                      none
% 1.06/1.04  --res_ordering                          kbo
% 1.06/1.04  --res_to_prop_solver                    active
% 1.06/1.04  --res_prop_simpl_new                    false
% 1.06/1.04  --res_prop_simpl_given                  true
% 1.06/1.04  --res_passive_queue_type                priority_queues
% 1.06/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.06/1.04  --res_passive_queues_freq               [15;5]
% 1.06/1.04  --res_forward_subs                      full
% 1.06/1.04  --res_backward_subs                     full
% 1.06/1.04  --res_forward_subs_resolution           true
% 1.06/1.04  --res_backward_subs_resolution          true
% 1.06/1.04  --res_orphan_elimination                true
% 1.06/1.04  --res_time_limit                        2.
% 1.06/1.04  --res_out_proof                         true
% 1.06/1.04  
% 1.06/1.04  ------ Superposition Options
% 1.06/1.04  
% 1.06/1.04  --superposition_flag                    true
% 1.06/1.04  --sup_passive_queue_type                priority_queues
% 1.06/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.06/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.06/1.04  --demod_completeness_check              fast
% 1.06/1.04  --demod_use_ground                      true
% 1.06/1.04  --sup_to_prop_solver                    passive
% 1.06/1.04  --sup_prop_simpl_new                    true
% 1.06/1.04  --sup_prop_simpl_given                  true
% 1.06/1.04  --sup_fun_splitting                     false
% 1.06/1.04  --sup_smt_interval                      50000
% 1.06/1.04  
% 1.06/1.04  ------ Superposition Simplification Setup
% 1.06/1.04  
% 1.06/1.04  --sup_indices_passive                   []
% 1.06/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.06/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.04  --sup_full_bw                           [BwDemod]
% 1.06/1.04  --sup_immed_triv                        [TrivRules]
% 1.06/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.06/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.04  --sup_immed_bw_main                     []
% 1.06/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.06/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.04  
% 1.06/1.04  ------ Combination Options
% 1.06/1.04  
% 1.06/1.04  --comb_res_mult                         3
% 1.06/1.04  --comb_sup_mult                         2
% 1.06/1.04  --comb_inst_mult                        10
% 1.06/1.04  
% 1.06/1.04  ------ Debug Options
% 1.06/1.04  
% 1.06/1.04  --dbg_backtrace                         false
% 1.06/1.04  --dbg_dump_prop_clauses                 false
% 1.06/1.04  --dbg_dump_prop_clauses_file            -
% 1.06/1.04  --dbg_out_stat                          false
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  ------ Proving...
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  % SZS status Theorem for theBenchmark.p
% 1.06/1.04  
% 1.06/1.04   Resolution empty clause
% 1.06/1.04  
% 1.06/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.06/1.04  
% 1.06/1.04  fof(f8,conjecture,(
% 1.06/1.04    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f9,negated_conjecture,(
% 1.06/1.04    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 1.06/1.04    inference(negated_conjecture,[],[f8])).
% 1.06/1.04  
% 1.06/1.04  fof(f23,plain,(
% 1.06/1.04    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.06/1.04    inference(ennf_transformation,[],[f9])).
% 1.06/1.04  
% 1.06/1.04  fof(f24,plain,(
% 1.06/1.04    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f23])).
% 1.06/1.04  
% 1.06/1.04  fof(f29,plain,(
% 1.06/1.04    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 1.06/1.04    introduced(choice_axiom,[])).
% 1.06/1.04  
% 1.06/1.04  fof(f28,plain,(
% 1.06/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 1.06/1.04    introduced(choice_axiom,[])).
% 1.06/1.04  
% 1.06/1.04  fof(f27,plain,(
% 1.06/1.04    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 1.06/1.04    introduced(choice_axiom,[])).
% 1.06/1.04  
% 1.06/1.04  fof(f26,plain,(
% 1.06/1.04    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 1.06/1.04    introduced(choice_axiom,[])).
% 1.06/1.04  
% 1.06/1.04  fof(f25,plain,(
% 1.06/1.04    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.06/1.04    introduced(choice_axiom,[])).
% 1.06/1.04  
% 1.06/1.04  fof(f30,plain,(
% 1.06/1.04    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.06/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f29,f28,f27,f26,f25])).
% 1.06/1.04  
% 1.06/1.04  fof(f47,plain,(
% 1.06/1.04    m1_subset_1(sK5,sK1)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f5,axiom,(
% 1.06/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f17,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.06/1.04    inference(ennf_transformation,[],[f5])).
% 1.06/1.04  
% 1.06/1.04  fof(f18,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f17])).
% 1.06/1.04  
% 1.06/1.04  fof(f35,plain,(
% 1.06/1.04    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f18])).
% 1.06/1.04  
% 1.06/1.04  fof(f43,plain,(
% 1.06/1.04    v1_funct_2(sK3,sK1,sK0)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f41,plain,(
% 1.06/1.04    ~v1_xboole_0(sK1)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f42,plain,(
% 1.06/1.04    v1_funct_1(sK3)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f44,plain,(
% 1.06/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f3,axiom,(
% 1.06/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f13,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.06/1.04    inference(ennf_transformation,[],[f3])).
% 1.06/1.04  
% 1.06/1.04  fof(f14,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f13])).
% 1.06/1.04  
% 1.06/1.04  fof(f33,plain,(
% 1.06/1.04    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f14])).
% 1.06/1.04  
% 1.06/1.04  fof(f46,plain,(
% 1.06/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f4,axiom,(
% 1.06/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f15,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.06/1.04    inference(ennf_transformation,[],[f4])).
% 1.06/1.04  
% 1.06/1.04  fof(f16,plain,(
% 1.06/1.04    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f15])).
% 1.06/1.04  
% 1.06/1.04  fof(f34,plain,(
% 1.06/1.04    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f16])).
% 1.06/1.04  
% 1.06/1.04  fof(f6,axiom,(
% 1.06/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f19,plain,(
% 1.06/1.04    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.06/1.04    inference(ennf_transformation,[],[f6])).
% 1.06/1.04  
% 1.06/1.04  fof(f20,plain,(
% 1.06/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.06/1.04    inference(flattening,[],[f19])).
% 1.06/1.04  
% 1.06/1.04  fof(f37,plain,(
% 1.06/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f20])).
% 1.06/1.04  
% 1.06/1.04  fof(f48,plain,(
% 1.06/1.04    v1_partfun1(sK4,sK0)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f45,plain,(
% 1.06/1.04    v1_funct_1(sK4)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f40,plain,(
% 1.06/1.04    ~v1_xboole_0(sK0)),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  fof(f2,axiom,(
% 1.06/1.04    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f11,plain,(
% 1.06/1.04    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.06/1.04    inference(ennf_transformation,[],[f2])).
% 1.06/1.04  
% 1.06/1.04  fof(f12,plain,(
% 1.06/1.04    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f11])).
% 1.06/1.04  
% 1.06/1.04  fof(f32,plain,(
% 1.06/1.04    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f12])).
% 1.06/1.04  
% 1.06/1.04  fof(f7,axiom,(
% 1.06/1.04    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 1.06/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.06/1.04  
% 1.06/1.04  fof(f21,plain,(
% 1.06/1.04    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.06/1.04    inference(ennf_transformation,[],[f7])).
% 1.06/1.04  
% 1.06/1.04  fof(f22,plain,(
% 1.06/1.04    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.06/1.04    inference(flattening,[],[f21])).
% 1.06/1.04  
% 1.06/1.04  fof(f39,plain,(
% 1.06/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.06/1.04    inference(cnf_transformation,[],[f22])).
% 1.06/1.04  
% 1.06/1.04  fof(f49,plain,(
% 1.06/1.04    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 1.06/1.04    inference(cnf_transformation,[],[f30])).
% 1.06/1.04  
% 1.06/1.04  cnf(c_11,negated_conjecture,
% 1.06/1.04      ( m1_subset_1(sK5,sK1) ),
% 1.06/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_951,plain,
% 1.06/1.04      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_4,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X3,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.06/1.04      inference(cnf_transformation,[],[f35]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_15,negated_conjecture,
% 1.06/1.04      ( v1_funct_2(sK3,sK1,sK0) ),
% 1.06/1.04      inference(cnf_transformation,[],[f43]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_473,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,X1)
% 1.06/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.06/1.04      | ~ v1_funct_1(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.06/1.04      | sK3 != X2
% 1.06/1.04      | sK0 != X3
% 1.06/1.04      | sK1 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_474,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.06/1.04      | ~ v1_funct_1(sK3)
% 1.06/1.04      | v1_xboole_0(sK1)
% 1.06/1.04      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_473]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_17,negated_conjecture,
% 1.06/1.04      ( ~ v1_xboole_0(sK1) ),
% 1.06/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_16,negated_conjecture,
% 1.06/1.04      ( v1_funct_1(sK3) ),
% 1.06/1.04      inference(cnf_transformation,[],[f42]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_14,negated_conjecture,
% 1.06/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.06/1.04      inference(cnf_transformation,[],[f44]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_478,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_474,c_17,c_16,c_14]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_948,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 1.06/1.04      | m1_subset_1(X0,sK1) != iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1128,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_951,c_948]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_2,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X3,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | v1_xboole_0(X1) ),
% 1.06/1.04      inference(cnf_transformation,[],[f33]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_509,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,X1)
% 1.06/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.06/1.04      | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
% 1.06/1.04      | ~ v1_funct_1(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | sK3 != X2
% 1.06/1.04      | sK0 != X3
% 1.06/1.04      | sK1 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_510,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
% 1.06/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.06/1.04      | ~ v1_funct_1(sK3)
% 1.06/1.04      | v1_xboole_0(sK1) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_509]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_514,plain,
% 1.06/1.04      ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~ m1_subset_1(X0,sK1) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_510,c_17,c_16,c_14]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_515,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_514]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_946,plain,
% 1.06/1.04      ( m1_subset_1(X0,sK1) != iProver_top
% 1.06/1.04      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) = iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1187,plain,
% 1.06/1.04      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 1.06/1.04      | m1_subset_1(sK5,sK1) != iProver_top ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_1128,c_946]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_26,plain,
% 1.06/1.04      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1313,plain,
% 1.06/1.04      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 1.06/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1187,c_26]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_12,negated_conjecture,
% 1.06/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.06/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_950,plain,
% 1.06/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_3,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X3,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | v1_xboole_0(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 1.06/1.04      inference(cnf_transformation,[],[f34]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_6,plain,
% 1.06/1.04      ( v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_partfun1(X0,X1)
% 1.06/1.04      | ~ v1_funct_1(X0) ),
% 1.06/1.04      inference(cnf_transformation,[],[f37]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_10,negated_conjecture,
% 1.06/1.04      ( v1_partfun1(sK4,sK0) ),
% 1.06/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_170,plain,
% 1.06/1.04      ( v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | sK4 != X0
% 1.06/1.04      | sK0 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_171,plain,
% 1.06/1.04      ( v1_funct_2(sK4,sK0,X0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.06/1.04      | ~ v1_funct_1(sK4) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_170]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_13,negated_conjecture,
% 1.06/1.04      ( v1_funct_1(sK4) ),
% 1.06/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_175,plain,
% 1.06/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.06/1.04      | v1_funct_2(sK4,sK0,X0) ),
% 1.06/1.04      inference(global_propositional_subsumption,[status(thm)],[c_171,c_13]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_176,plain,
% 1.06/1.04      ( v1_funct_2(sK4,sK0,X0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_175]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_548,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,X1)
% 1.06/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
% 1.06/1.04      | ~ v1_funct_1(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | v1_xboole_0(X3)
% 1.06/1.04      | X4 != X3
% 1.06/1.04      | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
% 1.06/1.04      | sK4 != X2
% 1.06/1.04      | sK0 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_176]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_549,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | ~ v1_funct_1(sK4)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | v1_xboole_0(sK0)
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_548]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_18,negated_conjecture,
% 1.06/1.04      ( ~ v1_xboole_0(sK0) ),
% 1.06/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_553,plain,
% 1.06/1.04      ( v1_xboole_0(X1)
% 1.06/1.04      | ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_549,c_18,c_13]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_554,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_553]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_partfun1(X0,X1)
% 1.06/1.04      | ~ v1_xboole_0(X2)
% 1.06/1.04      | v1_xboole_0(X1) ),
% 1.06/1.04      inference(cnf_transformation,[],[f32]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_188,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_xboole_0(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | sK4 != X0
% 1.06/1.04      | sK0 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_189,plain,
% 1.06/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.06/1.04      | ~ v1_xboole_0(X0)
% 1.06/1.04      | v1_xboole_0(sK0) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_188]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_191,plain,
% 1.06/1.04      ( ~ v1_xboole_0(X0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 1.06/1.04      inference(global_propositional_subsumption,[status(thm)],[c_189,c_18]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_192,plain,
% 1.06/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.06/1.04      | ~ v1_xboole_0(X0) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_191]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_567,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k7_partfun1(X1,sK4,X0) ),
% 1.06/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_554,c_192]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_944,plain,
% 1.06/1.04      ( k3_funct_2(sK0,X0,sK4,X1) = k7_partfun1(X0,sK4,X1)
% 1.06/1.04      | m1_subset_1(X1,sK0) != iProver_top
% 1.06/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1706,plain,
% 1.06/1.04      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 1.06/1.04      | m1_subset_1(X0,sK0) != iProver_top ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_950,c_944]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1794,plain,
% 1.06/1.04      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_1313,c_1706]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_527,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,X1)
% 1.06/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
% 1.06/1.04      | ~ v1_funct_1(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | X4 != X3
% 1.06/1.04      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.06/1.04      | sK4 != X2
% 1.06/1.04      | sK0 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_176]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_528,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | ~ v1_funct_1(sK4)
% 1.06/1.04      | v1_xboole_0(sK0)
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_527]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_532,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK0)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | k3_funct_2(sK0,X1,sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_528,c_18,c_13]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_945,plain,
% 1.06/1.04      ( k3_funct_2(sK0,X0,sK4,X1) = k1_funct_1(sK4,X1)
% 1.06/1.04      | m1_subset_1(X1,sK0) != iProver_top
% 1.06/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1647,plain,
% 1.06/1.04      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 1.06/1.04      | m1_subset_1(X0,sK0) != iProver_top ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_950,c_945]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1715,plain,
% 1.06/1.04      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_1313,c_1647]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1838,plain,
% 1.06/1.04      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(light_normalisation,[status(thm)],[c_1794,c_1715]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_8,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X3,X1)
% 1.06/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ v1_partfun1(X4,X2)
% 1.06/1.04      | ~ v1_funct_1(X4)
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | v1_xboole_0(X2)
% 1.06/1.04      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k3_funct_2(X1,X2,X0,X3)) ),
% 1.06/1.04      inference(cnf_transformation,[],[f39]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_202,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.06/1.04      | ~ m1_subset_1(X3,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.06/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | ~ v1_funct_1(X4)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | v1_xboole_0(X2)
% 1.06/1.04      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k3_funct_2(X1,X2,X0,X3))
% 1.06/1.04      | sK4 != X4
% 1.06/1.04      | sK0 != X2 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_203,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,sK0)
% 1.06/1.04      | ~ m1_subset_1(X2,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | ~ v1_funct_1(sK4)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | v1_xboole_0(sK0)
% 1.06/1.04      | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_202]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_207,plain,
% 1.06/1.04      ( v1_xboole_0(X1)
% 1.06/1.04      | ~ v1_funct_2(X0,X1,sK0)
% 1.06/1.04      | ~ m1_subset_1(X2,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_203,c_18,c_13]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_208,plain,
% 1.06/1.04      ( ~ v1_funct_2(X0,X1,sK0)
% 1.06/1.04      | ~ m1_subset_1(X2,X1)
% 1.06/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 1.06/1.04      | ~ v1_funct_1(X0)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_207]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_595,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,X1)
% 1.06/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 1.06/1.04      | ~ v1_funct_1(X2)
% 1.06/1.04      | v1_xboole_0(X1)
% 1.06/1.04      | k3_funct_2(X1,X3,k8_funct_2(X1,sK0,X3,X2,sK4),X0) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X2,X0))
% 1.06/1.04      | sK3 != X2
% 1.06/1.04      | sK0 != sK0
% 1.06/1.04      | sK1 != X1 ),
% 1.06/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_208]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_596,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.06/1.04      | ~ v1_funct_1(sK3)
% 1.06/1.04      | v1_xboole_0(sK1)
% 1.06/1.04      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
% 1.06/1.04      inference(unflattening,[status(thm)],[c_595]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_600,plain,
% 1.06/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
% 1.06/1.04      inference(global_propositional_subsumption,
% 1.06/1.04                [status(thm)],
% 1.06/1.04                [c_596,c_17,c_16,c_14]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_601,plain,
% 1.06/1.04      ( ~ m1_subset_1(X0,sK1)
% 1.06/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 1.06/1.04      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
% 1.06/1.04      inference(renaming,[status(thm)],[c_600]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_942,plain,
% 1.06/1.04      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,sK4),X1) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X1))
% 1.06/1.04      | m1_subset_1(X1,sK1) != iProver_top
% 1.06/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 1.06/1.04      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1394,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
% 1.06/1.04      | m1_subset_1(X0,sK1) != iProver_top ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_950,c_942]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1466,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 1.06/1.04      inference(superposition,[status(thm)],[c_951,c_1394]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1467,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(light_normalisation,[status(thm)],[c_1466,c_1128]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_9,negated_conjecture,
% 1.06/1.04      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 1.06/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1186,plain,
% 1.06/1.04      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(demodulation,[status(thm)],[c_1128,c_9]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1542,plain,
% 1.06/1.04      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.06/1.04      inference(demodulation,[status(thm)],[c_1467,c_1186]) ).
% 1.06/1.04  
% 1.06/1.04  cnf(c_1840,plain,
% 1.06/1.04      ( $false ),
% 1.06/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_1838,c_1542]) ).
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.06/1.04  
% 1.06/1.04  ------                               Statistics
% 1.06/1.04  
% 1.06/1.04  ------ General
% 1.06/1.04  
% 1.06/1.04  abstr_ref_over_cycles:                  0
% 1.06/1.04  abstr_ref_under_cycles:                 0
% 1.06/1.04  gc_basic_clause_elim:                   0
% 1.06/1.04  forced_gc_time:                         0
% 1.06/1.04  parsing_time:                           0.01
% 1.06/1.04  unif_index_cands_time:                  0.
% 1.06/1.04  unif_index_add_time:                    0.
% 1.06/1.04  orderings_time:                         0.
% 1.06/1.04  out_proof_time:                         0.011
% 1.06/1.04  total_time:                             0.122
% 1.06/1.04  num_of_symbols:                         48
% 1.06/1.04  num_of_terms:                           1884
% 1.06/1.04  
% 1.06/1.04  ------ Preprocessing
% 1.06/1.04  
% 1.06/1.04  num_of_splits:                          0
% 1.06/1.04  num_of_split_atoms:                     0
% 1.06/1.04  num_of_reused_defs:                     0
% 1.06/1.04  num_eq_ax_congr_red:                    1
% 1.06/1.04  num_of_sem_filtered_clauses:            1
% 1.06/1.04  num_of_subtypes:                        0
% 1.06/1.04  monotx_restored_types:                  0
% 1.06/1.04  sat_num_of_epr_types:                   0
% 1.06/1.04  sat_num_of_non_cyclic_types:            0
% 1.06/1.04  sat_guarded_non_collapsed_types:        0
% 1.06/1.04  num_pure_diseq_elim:                    0
% 1.06/1.04  simp_replaced_by:                       0
% 1.06/1.04  res_preprocessed:                       75
% 1.06/1.04  prep_upred:                             0
% 1.06/1.04  prep_unflattend:                        37
% 1.06/1.04  smt_new_axioms:                         0
% 1.06/1.04  pred_elim_cands:                        1
% 1.06/1.04  pred_elim:                              4
% 1.06/1.04  pred_elim_cl:                           4
% 1.06/1.04  pred_elim_cycles:                       7
% 1.06/1.04  merged_defs:                            0
% 1.06/1.04  merged_defs_ncl:                        0
% 1.06/1.04  bin_hyper_res:                          0
% 1.06/1.04  prep_cycles:                            4
% 1.06/1.04  pred_elim_time:                         0.017
% 1.06/1.04  splitting_time:                         0.
% 1.06/1.04  sem_filter_time:                        0.
% 1.06/1.04  monotx_time:                            0.001
% 1.06/1.04  subtype_inf_time:                       0.
% 1.06/1.04  
% 1.06/1.04  ------ Problem properties
% 1.06/1.04  
% 1.06/1.04  clauses:                                13
% 1.06/1.04  conjectures:                            4
% 1.06/1.04  epr:                                    1
% 1.06/1.04  horn:                                   13
% 1.06/1.04  ground:                                 4
% 1.06/1.04  unary:                                  4
% 1.06/1.04  binary:                                 4
% 1.06/1.04  lits:                                   28
% 1.06/1.04  lits_eq:                                9
% 1.06/1.04  fd_pure:                                0
% 1.06/1.04  fd_pseudo:                              0
% 1.06/1.04  fd_cond:                                0
% 1.06/1.04  fd_pseudo_cond:                         1
% 1.06/1.04  ac_symbols:                             0
% 1.06/1.04  
% 1.06/1.04  ------ Propositional Solver
% 1.06/1.04  
% 1.06/1.04  prop_solver_calls:                      27
% 1.06/1.04  prop_fast_solver_calls:                 576
% 1.06/1.04  smt_solver_calls:                       0
% 1.06/1.04  smt_fast_solver_calls:                  0
% 1.06/1.04  prop_num_of_clauses:                    659
% 1.06/1.04  prop_preprocess_simplified:             2544
% 1.06/1.04  prop_fo_subsumed:                       26
% 1.06/1.04  prop_solver_time:                       0.
% 1.06/1.04  smt_solver_time:                        0.
% 1.06/1.04  smt_fast_solver_time:                   0.
% 1.06/1.04  prop_fast_solver_time:                  0.
% 1.06/1.04  prop_unsat_core_time:                   0.
% 1.06/1.04  
% 1.06/1.04  ------ QBF
% 1.06/1.04  
% 1.06/1.04  qbf_q_res:                              0
% 1.06/1.04  qbf_num_tautologies:                    0
% 1.06/1.04  qbf_prep_cycles:                        0
% 1.06/1.04  
% 1.06/1.04  ------ BMC1
% 1.06/1.04  
% 1.06/1.04  bmc1_current_bound:                     -1
% 1.06/1.04  bmc1_last_solved_bound:                 -1
% 1.06/1.04  bmc1_unsat_core_size:                   -1
% 1.06/1.04  bmc1_unsat_core_parents_size:           -1
% 1.06/1.04  bmc1_merge_next_fun:                    0
% 1.06/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.06/1.04  
% 1.06/1.04  ------ Instantiation
% 1.06/1.04  
% 1.06/1.04  inst_num_of_clauses:                    242
% 1.06/1.04  inst_num_in_passive:                    77
% 1.06/1.04  inst_num_in_active:                     128
% 1.06/1.04  inst_num_in_unprocessed:                37
% 1.06/1.04  inst_num_of_loops:                      130
% 1.06/1.04  inst_num_of_learning_restarts:          0
% 1.06/1.04  inst_num_moves_active_passive:          0
% 1.06/1.04  inst_lit_activity:                      0
% 1.06/1.04  inst_lit_activity_moves:                0
% 1.06/1.04  inst_num_tautologies:                   0
% 1.06/1.04  inst_num_prop_implied:                  0
% 1.06/1.04  inst_num_existing_simplified:           0
% 1.06/1.04  inst_num_eq_res_simplified:             0
% 1.06/1.04  inst_num_child_elim:                    0
% 1.06/1.04  inst_num_of_dismatching_blockings:      18
% 1.06/1.04  inst_num_of_non_proper_insts:           241
% 1.06/1.04  inst_num_of_duplicates:                 0
% 1.06/1.04  inst_inst_num_from_inst_to_res:         0
% 1.06/1.04  inst_dismatching_checking_time:         0.
% 1.06/1.04  
% 1.06/1.04  ------ Resolution
% 1.06/1.04  
% 1.06/1.04  res_num_of_clauses:                     0
% 1.06/1.04  res_num_in_passive:                     0
% 1.06/1.04  res_num_in_active:                      0
% 1.06/1.04  res_num_of_loops:                       79
% 1.06/1.04  res_forward_subset_subsumed:            43
% 1.06/1.04  res_backward_subset_subsumed:           2
% 1.06/1.04  res_forward_subsumed:                   0
% 1.06/1.04  res_backward_subsumed:                  0
% 1.06/1.04  res_forward_subsumption_resolution:     1
% 1.06/1.04  res_backward_subsumption_resolution:    0
% 1.06/1.04  res_clause_to_clause_subsumption:       53
% 1.06/1.04  res_orphan_elimination:                 0
% 1.06/1.04  res_tautology_del:                      32
% 1.06/1.04  res_num_eq_res_simplified:              0
% 1.06/1.04  res_num_sel_changes:                    0
% 1.06/1.04  res_moves_from_active_to_pass:          0
% 1.06/1.04  
% 1.06/1.04  ------ Superposition
% 1.06/1.04  
% 1.06/1.04  sup_time_total:                         0.
% 1.06/1.04  sup_time_generating:                    0.
% 1.06/1.04  sup_time_sim_full:                      0.
% 1.06/1.04  sup_time_sim_immed:                     0.
% 1.06/1.04  
% 1.06/1.04  sup_num_of_clauses:                     32
% 1.06/1.04  sup_num_in_active:                      22
% 1.06/1.04  sup_num_in_passive:                     10
% 1.06/1.04  sup_num_of_loops:                       24
% 1.06/1.04  sup_fw_superposition:                   13
% 1.06/1.04  sup_bw_superposition:                   5
% 1.06/1.04  sup_immediate_simplified:               2
% 1.06/1.04  sup_given_eliminated:                   0
% 1.06/1.04  comparisons_done:                       0
% 1.06/1.04  comparisons_avoided:                    0
% 1.06/1.04  
% 1.06/1.04  ------ Simplifications
% 1.06/1.04  
% 1.06/1.04  
% 1.06/1.04  sim_fw_subset_subsumed:                 0
% 1.06/1.04  sim_bw_subset_subsumed:                 0
% 1.06/1.04  sim_fw_subsumed:                        0
% 1.06/1.04  sim_bw_subsumed:                        0
% 1.06/1.04  sim_fw_subsumption_res:                 1
% 1.06/1.04  sim_bw_subsumption_res:                 0
% 1.06/1.04  sim_tautology_del:                      0
% 1.06/1.04  sim_eq_tautology_del:                   1
% 1.06/1.04  sim_eq_res_simp:                        0
% 1.06/1.04  sim_fw_demodulated:                     0
% 1.06/1.04  sim_bw_demodulated:                     2
% 1.06/1.04  sim_light_normalised:                   3
% 1.06/1.04  sim_joinable_taut:                      0
% 1.06/1.04  sim_joinable_simp:                      0
% 1.06/1.04  sim_ac_normalised:                      0
% 1.06/1.04  sim_smt_subsumption:                    0
% 1.06/1.04  
%------------------------------------------------------------------------------
