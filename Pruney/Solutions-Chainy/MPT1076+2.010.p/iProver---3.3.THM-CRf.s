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
% DateTime   : Thu Dec  3 12:10:22 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  145 (1068 expanded)
%              Number of clauses        :   83 ( 237 expanded)
%              Number of leaves         :   18 ( 408 expanded)
%              Depth                    :   18
%              Number of atoms          :  592 (8679 expanded)
%              Number of equality atoms :  217 (1350 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f40,f39,f38,f37,f36])).

fof(f66,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1938,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1935,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1942,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3527,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1935,c_1942])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_25,c_24,c_22])).

cnf(c_768,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_4022,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3527,c_768])).

cnf(c_4029,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1938,c_4022])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1943,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4052,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_1943])).

cnf(c_28,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4462,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4052,c_28,c_29,c_30,c_31,c_34])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1937,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1941,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3471,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_1941])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2190,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2298,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2332,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_2333,plain,
    ( v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2332])).

cnf(c_1498,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2666,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_2668,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2666])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_322,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_12,c_2,c_1])).

cnf(c_327,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_1930,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_2630,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_partfun1(sK4,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_1930])).

cnf(c_2195,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_2263,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_2722,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2630,c_20,c_18,c_2263])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1951,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2531,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1937,c_1951])).

cnf(c_2725,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_2722,c_2531])).

cnf(c_8,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1946,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3507,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK0,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_1946])).

cnf(c_4233,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3471,c_26,c_27,c_32,c_20,c_33,c_18,c_35,c_0,c_2332,c_2333,c_2668,c_3507])).

cnf(c_4234,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4233])).

cnf(c_4467,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_4462,c_4234])).

cnf(c_3526,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_1942])).

cnf(c_3951,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3526,c_26,c_27,c_32,c_20,c_33,c_18,c_0,c_2332,c_2668,c_3507])).

cnf(c_4468,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_4462,c_3951])).

cnf(c_4471,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_4467,c_4468])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X3,X2)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1940,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X0,X2,X3,X5))
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_partfun1(X4,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2848,plain,
    ( k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_1940])).

cnf(c_3121,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2848,c_27,c_32,c_35])).

cnf(c_3122,plain,
    ( k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3121])).

cnf(c_3131,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1935,c_3122])).

cnf(c_3185,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3131,c_28,c_29,c_30])).

cnf(c_3193,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1938,c_3185])).

cnf(c_17,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3195,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3193,c_17])).

cnf(c_4046,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_4029,c_3195])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4471,c_4046])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.17/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.98  
% 2.17/0.98  ------  iProver source info
% 2.17/0.98  
% 2.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.98  git: non_committed_changes: false
% 2.17/0.98  git: last_make_outside_of_git: false
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     num_symb
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       true
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  ------ Parsing...
% 2.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.98  ------ Proving...
% 2.17/0.98  ------ Problem Properties 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  clauses                                 25
% 2.17/0.98  conjectures                             10
% 2.17/0.98  EPR                                     8
% 2.17/0.98  Horn                                    17
% 2.17/0.98  unary                                   11
% 2.17/0.98  binary                                  2
% 2.17/0.98  lits                                    72
% 2.17/0.98  lits eq                                 15
% 2.17/0.98  fd_pure                                 0
% 2.17/0.98  fd_pseudo                               0
% 2.17/0.98  fd_cond                                 3
% 2.17/0.98  fd_pseudo_cond                          1
% 2.17/0.98  AC symbols                              0
% 2.17/0.98  
% 2.17/0.98  ------ Schedule dynamic 5 is on 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  Current options:
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     none
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       false
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ Proving...
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS status Theorem for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  fof(f12,conjecture,(
% 2.17/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f13,negated_conjecture,(
% 2.17/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.17/0.98    inference(negated_conjecture,[],[f12])).
% 2.17/0.98  
% 2.17/0.98  fof(f32,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f13])).
% 2.17/0.98  
% 2.17/0.98  fof(f33,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f32])).
% 2.17/0.98  
% 2.17/0.98  fof(f40,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f39,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f38,plain,(
% 2.17/0.98    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f37,plain,(
% 2.17/0.98    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f36,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f41,plain,(
% 2.17/0.98    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f40,f39,f38,f37,f36])).
% 2.17/0.98  
% 2.17/0.98  fof(f66,plain,(
% 2.17/0.98    m1_subset_1(sK5,sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f63,plain,(
% 2.17/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f9,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f26,plain,(
% 2.17/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f9])).
% 2.17/0.98  
% 2.17/0.98  fof(f27,plain,(
% 2.17/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f26])).
% 2.17/0.98  
% 2.17/0.98  fof(f56,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f27])).
% 2.17/0.98  
% 2.17/0.98  fof(f62,plain,(
% 2.17/0.98    v1_funct_2(sK3,sK1,sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f60,plain,(
% 2.17/0.98    ~v1_xboole_0(sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f61,plain,(
% 2.17/0.98    v1_funct_1(sK3)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f8,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f24,plain,(
% 2.17/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f8])).
% 2.17/0.98  
% 2.17/0.98  fof(f25,plain,(
% 2.17/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f24])).
% 2.17/0.98  
% 2.17/0.98  fof(f55,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f25])).
% 2.17/0.98  
% 2.17/0.98  fof(f65,plain,(
% 2.17/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f10,axiom,(
% 2.17/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f28,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f10])).
% 2.17/0.98  
% 2.17/0.98  fof(f29,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f57,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f29])).
% 2.17/0.98  
% 2.17/0.98  fof(f59,plain,(
% 2.17/0.98    ~v1_xboole_0(sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f64,plain,(
% 2.17/0.98    v1_funct_1(sK4)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f67,plain,(
% 2.17/0.98    v1_partfun1(sK4,sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  fof(f1,axiom,(
% 2.17/0.98    v1_xboole_0(k1_xboole_0)),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f42,plain,(
% 2.17/0.98    v1_xboole_0(k1_xboole_0)),
% 2.17/0.98    inference(cnf_transformation,[],[f1])).
% 2.17/0.98  
% 2.17/0.98  fof(f5,axiom,(
% 2.17/0.98    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f18,plain,(
% 2.17/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f5])).
% 2.17/0.98  
% 2.17/0.98  fof(f19,plain,(
% 2.17/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f18])).
% 2.17/0.98  
% 2.17/0.98  fof(f46,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f19])).
% 2.17/0.98  
% 2.17/0.98  fof(f3,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f14,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.17/0.98    inference(pure_predicate_removal,[],[f3])).
% 2.17/0.98  
% 2.17/0.98  fof(f16,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(ennf_transformation,[],[f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f44,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f16])).
% 2.17/0.98  
% 2.17/0.98  fof(f7,axiom,(
% 2.17/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f22,plain,(
% 2.17/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.17/0.98    inference(ennf_transformation,[],[f7])).
% 2.17/0.98  
% 2.17/0.98  fof(f23,plain,(
% 2.17/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.17/0.98    inference(flattening,[],[f22])).
% 2.17/0.98  
% 2.17/0.98  fof(f35,plain,(
% 2.17/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.17/0.98    inference(nnf_transformation,[],[f23])).
% 2.17/0.98  
% 2.17/0.98  fof(f53,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f35])).
% 2.17/0.98  
% 2.17/0.98  fof(f2,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f15,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(ennf_transformation,[],[f2])).
% 2.17/0.98  
% 2.17/0.98  fof(f43,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f15])).
% 2.17/0.98  
% 2.17/0.98  fof(f4,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f17,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(ennf_transformation,[],[f4])).
% 2.17/0.98  
% 2.17/0.98  fof(f45,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f6,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f20,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(ennf_transformation,[],[f6])).
% 2.17/0.98  
% 2.17/0.98  fof(f21,plain,(
% 2.17/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(flattening,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f34,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.98    inference(nnf_transformation,[],[f21])).
% 2.17/0.98  
% 2.17/0.98  fof(f49,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f34])).
% 2.17/0.98  
% 2.17/0.98  fof(f11,axiom,(
% 2.17/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f30,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f11])).
% 2.17/0.98  
% 2.17/0.98  fof(f31,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.17/0.98    inference(flattening,[],[f30])).
% 2.17/0.98  
% 2.17/0.98  fof(f58,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f31])).
% 2.17/0.98  
% 2.17/0.98  fof(f68,plain,(
% 2.17/0.98    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.17/0.98    inference(cnf_transformation,[],[f41])).
% 2.17/0.98  
% 2.17/0.98  cnf(c_19,negated_conjecture,
% 2.17/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1938,plain,
% 2.17/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_22,negated_conjecture,
% 2.17/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.17/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1935,plain,
% 2.17/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_14,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X3,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | v1_xboole_0(X1)
% 2.17/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.17/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1942,plain,
% 2.17/0.98      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 2.17/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.17/0.98      | m1_subset_1(X3,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.17/0.98      | v1_funct_1(X2) != iProver_top
% 2.17/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3527,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 2.17/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 2.17/0.98      | v1_funct_1(sK3) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1935,c_1942]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_23,negated_conjecture,
% 2.17/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_761,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.17/0.98      | ~ v1_funct_1(X2)
% 2.17/0.98      | v1_xboole_0(X1)
% 2.17/0.98      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.17/0.98      | sK3 != X2
% 2.17/0.98      | sK0 != X3
% 2.17/0.98      | sK1 != X1 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_762,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,sK1)
% 2.17/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.17/0.98      | ~ v1_funct_1(sK3)
% 2.17/0.98      | v1_xboole_0(sK1)
% 2.17/0.98      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_761]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_25,negated_conjecture,
% 2.17/0.98      ( ~ v1_xboole_0(sK1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_24,negated_conjecture,
% 2.17/0.98      ( v1_funct_1(sK3) ),
% 2.17/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_766,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,sK1)
% 2.17/0.98      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_762,c_25,c_24,c_22]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_768,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 2.17/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4022,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 2.17/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_3527,c_768]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4029,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1938,c_4022]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_13,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X3,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | v1_xboole_0(X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1943,plain,
% 2.17/0.98      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.17/0.98      | m1_subset_1(X3,X1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.17/0.98      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 2.17/0.98      | v1_funct_1(X0) != iProver_top
% 2.17/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4052,plain,
% 2.17/0.98      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 2.17/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.17/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.17/0.98      | v1_funct_1(sK3) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_4029,c_1943]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_28,plain,
% 2.17/0.98      ( v1_xboole_0(sK1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_29,plain,
% 2.17/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_30,plain,
% 2.17/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_31,plain,
% 2.17/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_34,plain,
% 2.17/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4462,plain,
% 2.17/0.98      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_4052,c_28,c_29,c_30,c_31,c_34]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_20,negated_conjecture,
% 2.17/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.17/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1937,plain,
% 2.17/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X3,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | v1_xboole_0(X2)
% 2.17/0.98      | v1_xboole_0(X1)
% 2.17/0.98      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 2.17/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1941,plain,
% 2.17/0.98      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
% 2.17/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.17/0.98      | m1_subset_1(X3,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.17/0.98      | v1_funct_1(X2) != iProver_top
% 2.17/0.98      | v1_xboole_0(X0) = iProver_top
% 2.17/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3471,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 2.17/0.98      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,sK0) != iProver_top
% 2.17/0.98      | v1_funct_1(sK4) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK0) = iProver_top
% 2.17/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1937,c_1941]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_26,negated_conjecture,
% 2.17/0.98      ( ~ v1_xboole_0(sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_27,plain,
% 2.17/0.98      ( v1_xboole_0(sK0) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_21,negated_conjecture,
% 2.17/0.98      ( v1_funct_1(sK4) ),
% 2.17/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_32,plain,
% 2.17/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_33,plain,
% 2.17/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_18,negated_conjecture,
% 2.17/0.98      ( v1_partfun1(sK4,sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_35,plain,
% 2.17/0.98      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_0,plain,
% 2.17/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4,plain,
% 2.17/0.98      ( ~ v1_partfun1(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_xboole_0(X2)
% 2.17/0.98      | v1_xboole_0(X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2190,plain,
% 2.17/0.98      ( ~ v1_partfun1(X0,sK0)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.17/0.98      | ~ v1_xboole_0(X1)
% 2.17/0.98      | v1_xboole_0(sK0) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2298,plain,
% 2.17/0.98      ( ~ v1_partfun1(sK4,sK0)
% 2.17/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.17/0.98      | ~ v1_xboole_0(X0)
% 2.17/0.98      | v1_xboole_0(sK0) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_2190]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2332,plain,
% 2.17/0.98      ( ~ v1_partfun1(sK4,sK0)
% 2.17/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.17/0.98      | v1_xboole_0(sK0)
% 2.17/0.98      | ~ v1_xboole_0(sK2) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_2298]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2333,plain,
% 2.17/0.98      ( v1_partfun1(sK4,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK0) = iProver_top
% 2.17/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_2332]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1498,plain,
% 2.17/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.17/0.98      theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2666,plain,
% 2.17/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_1498]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2668,plain,
% 2.17/0.98      ( v1_xboole_0(sK2)
% 2.17/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.17/0.98      | sK2 != k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_2666]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2,plain,
% 2.17/0.98      ( v4_relat_1(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.17/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_12,plain,
% 2.17/0.98      ( ~ v1_partfun1(X0,X1)
% 2.17/0.98      | ~ v4_relat_1(X0,X1)
% 2.17/0.98      | ~ v1_relat_1(X0)
% 2.17/0.98      | k1_relat_1(X0) = X1 ),
% 2.17/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_322,plain,
% 2.17/0.98      ( ~ v1_partfun1(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_relat_1(X0)
% 2.17/0.98      | k1_relat_1(X0) = X1 ),
% 2.17/0.98      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | v1_relat_1(X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_326,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_partfun1(X0,X1)
% 2.17/0.98      | k1_relat_1(X0) = X1 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_322,c_12,c_2,c_1]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_327,plain,
% 2.17/0.98      ( ~ v1_partfun1(X0,X1)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | k1_relat_1(X0) = X1 ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_326]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1930,plain,
% 2.17/0.98      ( k1_relat_1(X0) = X1
% 2.17/0.98      | v1_partfun1(X0,X1) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2630,plain,
% 2.17/0.98      ( k1_relat_1(sK4) = sK0 | v1_partfun1(sK4,sK0) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1937,c_1930]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2195,plain,
% 2.17/0.98      ( ~ v1_partfun1(sK4,sK0)
% 2.17/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.17/0.98      | k1_relat_1(sK4) = sK0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_327]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2263,plain,
% 2.17/0.98      ( ~ v1_partfun1(sK4,sK0)
% 2.17/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.17/0.98      | k1_relat_1(sK4) = sK0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_2195]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2722,plain,
% 2.17/0.98      ( k1_relat_1(sK4) = sK0 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2630,c_20,c_18,c_2263]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1951,plain,
% 2.17/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.17/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2531,plain,
% 2.17/0.98      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1937,c_1951]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2725,plain,
% 2.17/0.98      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_2722,c_2531]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_8,plain,
% 2.17/0.98      ( v1_funct_2(X0,X1,X2)
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.17/0.98      | k1_xboole_0 = X2 ),
% 2.17/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1946,plain,
% 2.17/0.98      ( k1_relset_1(X0,X1,X2) != X0
% 2.17/0.98      | k1_xboole_0 = X1
% 2.17/0.98      | v1_funct_2(X2,X0,X1) = iProver_top
% 2.17/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3507,plain,
% 2.17/0.98      ( sK2 = k1_xboole_0
% 2.17/0.98      | v1_funct_2(sK4,sK0,sK2) = iProver_top
% 2.17/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_2725,c_1946]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4233,plain,
% 2.17/0.98      ( m1_subset_1(X0,sK0) != iProver_top
% 2.17/0.98      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_3471,c_26,c_27,c_32,c_20,c_33,c_18,c_35,c_0,c_2332,
% 2.17/0.98                 c_2333,c_2668,c_3507]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4234,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 2.17/0.98      | m1_subset_1(X0,sK0) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_4233]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4467,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_4462,c_4234]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3526,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 2.17/0.98      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,sK0) != iProver_top
% 2.17/0.98      | v1_funct_1(sK4) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1937,c_1942]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3951,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 2.17/0.98      | m1_subset_1(X0,sK0) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_3526,c_26,c_27,c_32,c_20,c_33,c_18,c_0,c_2332,c_2668,
% 2.17/0.98                 c_3507]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4468,plain,
% 2.17/0.98      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_4462,c_3951]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4471,plain,
% 2.17/0.98      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_4467,c_4468]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_16,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.17/0.98      | ~ v1_partfun1(X3,X2)
% 2.17/0.98      | ~ m1_subset_1(X4,X1)
% 2.17/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.98      | ~ v1_funct_1(X3)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | v1_xboole_0(X1)
% 2.17/0.98      | v1_xboole_0(X2)
% 2.17/0.98      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1940,plain,
% 2.17/0.98      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X0,X2,X3,X5))
% 2.17/0.98      | v1_funct_2(X3,X0,X2) != iProver_top
% 2.17/0.98      | v1_partfun1(X4,X2) != iProver_top
% 2.17/0.98      | m1_subset_1(X5,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.17/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 2.17/0.98      | v1_funct_1(X4) != iProver_top
% 2.17/0.98      | v1_funct_1(X3) != iProver_top
% 2.17/0.98      | v1_xboole_0(X0) = iProver_top
% 2.17/0.98      | v1_xboole_0(X2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2848,plain,
% 2.17/0.98      ( k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
% 2.17/0.98      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.17/0.98      | v1_partfun1(sK4,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.17/0.98      | v1_funct_1(X1) != iProver_top
% 2.17/0.98      | v1_funct_1(sK4) != iProver_top
% 2.17/0.98      | v1_xboole_0(X0) = iProver_top
% 2.17/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1937,c_1940]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3121,plain,
% 2.17/0.98      ( v1_xboole_0(X0) = iProver_top
% 2.17/0.98      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.17/0.98      | k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
% 2.17/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.17/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2848,c_27,c_32,c_35]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3122,plain,
% 2.17/0.98      ( k3_funct_2(X0,sK2,k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X2))
% 2.17/0.98      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.17/0.98      | v1_funct_1(X1) != iProver_top
% 2.17/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_3121]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3131,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
% 2.17/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.17/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 2.17/0.98      | v1_funct_1(sK3) != iProver_top
% 2.17/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1935,c_3122]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3185,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))
% 2.17/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_3131,c_28,c_29,c_30]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3193,plain,
% 2.17/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1938,c_3185]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_17,negated_conjecture,
% 2.17/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3195,plain,
% 2.17/0.98      ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_3193,c_17]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4046,plain,
% 2.17/0.98      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_4029,c_3195]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(contradiction,plain,
% 2.17/0.98      ( $false ),
% 2.17/0.98      inference(minisat,[status(thm)],[c_4471,c_4046]) ).
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  ------                               Statistics
% 2.17/0.98  
% 2.17/0.98  ------ General
% 2.17/0.98  
% 2.17/0.98  abstr_ref_over_cycles:                  0
% 2.17/0.98  abstr_ref_under_cycles:                 0
% 2.17/0.98  gc_basic_clause_elim:                   0
% 2.17/0.98  forced_gc_time:                         0
% 2.17/0.98  parsing_time:                           0.011
% 2.17/0.98  unif_index_cands_time:                  0.
% 2.17/0.98  unif_index_add_time:                    0.
% 2.17/0.98  orderings_time:                         0.
% 2.17/0.98  out_proof_time:                         0.01
% 2.17/0.98  total_time:                             0.16
% 2.17/0.98  num_of_symbols:                         53
% 2.17/0.98  num_of_terms:                           5349
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing
% 2.17/0.98  
% 2.17/0.98  num_of_splits:                          0
% 2.17/0.98  num_of_split_atoms:                     0
% 2.17/0.98  num_of_reused_defs:                     0
% 2.17/0.98  num_eq_ax_congr_red:                    14
% 2.17/0.98  num_of_sem_filtered_clauses:            1
% 2.17/0.98  num_of_subtypes:                        0
% 2.17/0.98  monotx_restored_types:                  0
% 2.17/0.98  sat_num_of_epr_types:                   0
% 2.17/0.98  sat_num_of_non_cyclic_types:            0
% 2.17/0.98  sat_guarded_non_collapsed_types:        0
% 2.17/0.98  num_pure_diseq_elim:                    0
% 2.17/0.98  simp_replaced_by:                       0
% 2.17/0.98  res_preprocessed:                       131
% 2.17/0.98  prep_upred:                             0
% 2.17/0.98  prep_unflattend:                        152
% 2.17/0.98  smt_new_axioms:                         0
% 2.17/0.98  pred_elim_cands:                        5
% 2.17/0.98  pred_elim:                              2
% 2.17/0.98  pred_elim_cl:                           2
% 2.17/0.98  pred_elim_cycles:                       7
% 2.17/0.98  merged_defs:                            0
% 2.17/0.98  merged_defs_ncl:                        0
% 2.17/0.98  bin_hyper_res:                          0
% 2.17/0.98  prep_cycles:                            4
% 2.17/0.98  pred_elim_time:                         0.024
% 2.17/0.98  splitting_time:                         0.
% 2.17/0.98  sem_filter_time:                        0.
% 2.17/0.98  monotx_time:                            0.001
% 2.17/0.98  subtype_inf_time:                       0.
% 2.17/0.98  
% 2.17/0.98  ------ Problem properties
% 2.17/0.98  
% 2.17/0.98  clauses:                                25
% 2.17/0.98  conjectures:                            10
% 2.17/0.98  epr:                                    8
% 2.17/0.98  horn:                                   17
% 2.17/0.98  ground:                                 11
% 2.17/0.98  unary:                                  11
% 2.17/0.98  binary:                                 2
% 2.17/0.98  lits:                                   72
% 2.17/0.98  lits_eq:                                15
% 2.17/0.98  fd_pure:                                0
% 2.17/0.98  fd_pseudo:                              0
% 2.17/0.98  fd_cond:                                3
% 2.17/0.98  fd_pseudo_cond:                         1
% 2.17/0.98  ac_symbols:                             0
% 2.17/0.98  
% 2.17/0.98  ------ Propositional Solver
% 2.17/0.98  
% 2.17/0.98  prop_solver_calls:                      28
% 2.17/0.98  prop_fast_solver_calls:                 1232
% 2.17/0.98  smt_solver_calls:                       0
% 2.17/0.98  smt_fast_solver_calls:                  0
% 2.17/0.98  prop_num_of_clauses:                    1194
% 2.17/0.98  prop_preprocess_simplified:             4927
% 2.17/0.98  prop_fo_subsumed:                       71
% 2.17/0.98  prop_solver_time:                       0.
% 2.17/0.98  smt_solver_time:                        0.
% 2.17/0.98  smt_fast_solver_time:                   0.
% 2.17/0.98  prop_fast_solver_time:                  0.
% 2.17/0.98  prop_unsat_core_time:                   0.
% 2.17/0.98  
% 2.17/0.98  ------ QBF
% 2.17/0.98  
% 2.17/0.98  qbf_q_res:                              0
% 2.17/0.98  qbf_num_tautologies:                    0
% 2.17/0.98  qbf_prep_cycles:                        0
% 2.17/0.98  
% 2.17/0.98  ------ BMC1
% 2.17/0.98  
% 2.17/0.98  bmc1_current_bound:                     -1
% 2.17/0.98  bmc1_last_solved_bound:                 -1
% 2.17/0.98  bmc1_unsat_core_size:                   -1
% 2.17/0.98  bmc1_unsat_core_parents_size:           -1
% 2.17/0.98  bmc1_merge_next_fun:                    0
% 2.17/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation
% 2.17/0.98  
% 2.17/0.98  inst_num_of_clauses:                    355
% 2.17/0.98  inst_num_in_passive:                    86
% 2.17/0.98  inst_num_in_active:                     242
% 2.17/0.98  inst_num_in_unprocessed:                27
% 2.17/0.98  inst_num_of_loops:                      250
% 2.17/0.98  inst_num_of_learning_restarts:          0
% 2.17/0.98  inst_num_moves_active_passive:          5
% 2.17/0.98  inst_lit_activity:                      0
% 2.17/0.98  inst_lit_activity_moves:                0
% 2.17/0.98  inst_num_tautologies:                   0
% 2.17/0.98  inst_num_prop_implied:                  0
% 2.17/0.98  inst_num_existing_simplified:           0
% 2.17/0.98  inst_num_eq_res_simplified:             0
% 2.17/0.98  inst_num_child_elim:                    0
% 2.17/0.98  inst_num_of_dismatching_blockings:      27
% 2.17/0.98  inst_num_of_non_proper_insts:           256
% 2.17/0.98  inst_num_of_duplicates:                 0
% 2.17/0.98  inst_inst_num_from_inst_to_res:         0
% 2.17/0.98  inst_dismatching_checking_time:         0.
% 2.17/0.98  
% 2.17/0.98  ------ Resolution
% 2.17/0.98  
% 2.17/0.98  res_num_of_clauses:                     0
% 2.17/0.98  res_num_in_passive:                     0
% 2.17/0.98  res_num_in_active:                      0
% 2.17/0.98  res_num_of_loops:                       135
% 2.17/0.98  res_forward_subset_subsumed:            42
% 2.17/0.98  res_backward_subset_subsumed:           0
% 2.17/0.98  res_forward_subsumed:                   0
% 2.17/0.98  res_backward_subsumed:                  0
% 2.17/0.98  res_forward_subsumption_resolution:     1
% 2.17/0.98  res_backward_subsumption_resolution:    0
% 2.17/0.98  res_clause_to_clause_subsumption:       268
% 2.17/0.98  res_orphan_elimination:                 0
% 2.17/0.98  res_tautology_del:                      33
% 2.17/0.98  res_num_eq_res_simplified:              0
% 2.17/0.98  res_num_sel_changes:                    0
% 2.17/0.98  res_moves_from_active_to_pass:          0
% 2.17/0.98  
% 2.17/0.98  ------ Superposition
% 2.17/0.98  
% 2.17/0.98  sup_time_total:                         0.
% 2.17/0.98  sup_time_generating:                    0.
% 2.17/0.98  sup_time_sim_full:                      0.
% 2.17/0.98  sup_time_sim_immed:                     0.
% 2.17/0.98  
% 2.17/0.98  sup_num_of_clauses:                     63
% 2.17/0.98  sup_num_in_active:                      43
% 2.17/0.98  sup_num_in_passive:                     20
% 2.17/0.98  sup_num_of_loops:                       49
% 2.17/0.98  sup_fw_superposition:                   26
% 2.17/0.98  sup_bw_superposition:                   18
% 2.17/0.98  sup_immediate_simplified:               9
% 2.17/0.98  sup_given_eliminated:                   0
% 2.17/0.98  comparisons_done:                       0
% 2.17/0.98  comparisons_avoided:                    0
% 2.17/0.98  
% 2.17/0.98  ------ Simplifications
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  sim_fw_subset_subsumed:                 3
% 2.17/0.98  sim_bw_subset_subsumed:                 3
% 2.17/0.98  sim_fw_subsumed:                        1
% 2.17/0.98  sim_bw_subsumed:                        0
% 2.17/0.98  sim_fw_subsumption_res:                 0
% 2.17/0.98  sim_bw_subsumption_res:                 0
% 2.17/0.98  sim_tautology_del:                      0
% 2.17/0.98  sim_eq_tautology_del:                   0
% 2.17/0.98  sim_eq_res_simp:                        0
% 2.17/0.98  sim_fw_demodulated:                     1
% 2.17/0.98  sim_bw_demodulated:                     5
% 2.17/0.98  sim_light_normalised:                   4
% 2.17/0.98  sim_joinable_taut:                      0
% 2.17/0.98  sim_joinable_simp:                      0
% 2.17/0.98  sim_ac_normalised:                      0
% 2.17/0.98  sim_smt_subsumption:                    0
% 2.17/0.98  
%------------------------------------------------------------------------------
