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
% DateTime   : Thu Dec  3 12:10:25 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 930 expanded)
%              Number of clauses        :  124 ( 267 expanded)
%              Number of leaves         :   18 ( 332 expanded)
%              Depth                    :   22
%              Number of atoms          :  667 (7107 expanded)
%              Number of equality atoms :  190 (1037 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,conjecture,(
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
                       => k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
                         => k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5)
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5)
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) != k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5)
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
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
                    ( k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) != k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5)
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
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
                      ( k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5)
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

fof(f37,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f36,f35,f34,f33,f32])).

fof(f59,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
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
                       => k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_651,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK0 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_652,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK0 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_652])).

cnf(c_769,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_1060,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_769])).

cnf(c_1077,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1060])).

cnf(c_1527,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_1143,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1070,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1517,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1075,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1513,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_1827,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1513])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1074,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1857,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1858,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1060])).

cnf(c_1528,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_2346,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1528])).

cnf(c_2681,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1527,c_1143,c_1827,c_1858,c_2346])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_514,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_515,plain,
    ( ~ v5_relat_1(sK3,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X1),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1061,plain,
    ( ~ v5_relat_1(sK3,X0_51)
    | ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0_50),X0_51)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_515])).

cnf(c_1526,plain,
    ( v5_relat_1(sK3,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_1140,plain,
    ( v5_relat_1(sK3,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1069,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1518,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_1828,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1513])).

cnf(c_1860,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1861,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_2066,plain,
    ( r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | v5_relat_1(sK3,X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1526,c_1140,c_1828,c_1861])).

cnf(c_2067,plain,
    ( v5_relat_1(sK3,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_2066])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_442,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_443,plain,
    ( ~ v5_relat_1(sK4,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1064,plain,
    ( ~ v5_relat_1(sK4,X0_51)
    | ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_1523,plain,
    ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | v5_relat_1(sK4,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_1131,plain,
    ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | v5_relat_1(sK4,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_2076,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | v5_relat_1(sK4,X0_51) != iProver_top
    | k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1523,c_1131,c_1827,c_1858])).

cnf(c_2077,plain,
    ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | v5_relat_1(sK4,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2076])).

cnf(c_2085,plain,
    ( k7_partfun1(X0_51,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
    | v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top
    | v5_relat_1(sK4,X0_51) != iProver_top
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2077])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_369,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_370,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_372,plain,
    ( v1_partfun1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_22,c_20,c_18])).

cnf(c_664,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_372])).

cnf(c_665,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_665])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_786,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_788,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_18,c_786])).

cnf(c_1059,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_788])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | r2_hidden(X0_50,sK1) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1703,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1) ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_1704,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1073,plain,
    ( v5_relat_1(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1731,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_1732,plain,
    ( v5_relat_1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1731])).

cnf(c_1838,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1828])).

cnf(c_1086,plain,
    ( ~ r2_hidden(X0_50,X0_51)
    | r2_hidden(X1_50,X1_51)
    | X1_51 != X0_51
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1765,plain,
    ( r2_hidden(X0_50,X0_51)
    | ~ r2_hidden(sK5,sK1)
    | X0_51 != sK1
    | X0_50 != sK5 ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1980,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK1)
    | k1_relat_1(sK3) != sK1
    | X0_50 != sK5 ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_2137,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK1)
    | k1_relat_1(sK3) != sK1
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_2139,plain,
    ( k1_relat_1(sK3) != sK1
    | sK5 != sK5
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK5,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_1082,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2138,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1071,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1516,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_324,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
    | sK3 != X4
    | sK0 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_325,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_329,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_22,c_21,c_20,c_18])).

cnf(c_330,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_421,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_330,c_17])).

cnf(c_422,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_14])).

cnf(c_1065,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_1522,plain,
    ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_2189,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1522])).

cnf(c_2254,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1516,c_2189])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_21,c_20,c_18])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1519,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_1776,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1516,c_1519])).

cnf(c_2255,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2254,c_1776])).

cnf(c_13,negated_conjecture,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1072,negated_conjecture,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1901,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1776,c_1072])).

cnf(c_2257,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2255,c_1901])).

cnf(c_2351,plain,
    ( ~ v5_relat_1(sK3,X0_51)
    | r2_hidden(k1_funct_1(sK3,sK5),X0_51)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2384,plain,
    ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_2386,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_1893,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_partfun1(sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_2385,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_2388,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v5_relat_1(sK4,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2385])).

cnf(c_2426,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2085,c_29,c_30,c_1059,c_1704,c_1732,c_1827,c_1828,c_1838,c_1858,c_1860,c_1861,c_2139,c_2138,c_2257,c_2386,c_2388])).

cnf(c_2687,plain,
    ( v5_relat_1(sK3,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2681,c_2426])).

cnf(c_1734,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_1735,plain,
    ( v5_relat_1(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2687,c_1735,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.18/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.02  
% 2.18/1.02  ------  iProver source info
% 2.18/1.02  
% 2.18/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.02  git: non_committed_changes: false
% 2.18/1.02  git: last_make_outside_of_git: false
% 2.18/1.02  
% 2.18/1.02  ------ 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options
% 2.18/1.02  
% 2.18/1.02  --out_options                           all
% 2.18/1.02  --tptp_safe_out                         true
% 2.18/1.02  --problem_path                          ""
% 2.18/1.02  --include_path                          ""
% 2.18/1.02  --clausifier                            res/vclausify_rel
% 2.18/1.02  --clausifier_options                    --mode clausify
% 2.18/1.02  --stdin                                 false
% 2.18/1.02  --stats_out                             all
% 2.18/1.02  
% 2.18/1.02  ------ General Options
% 2.18/1.02  
% 2.18/1.02  --fof                                   false
% 2.18/1.02  --time_out_real                         305.
% 2.18/1.02  --time_out_virtual                      -1.
% 2.18/1.02  --symbol_type_check                     false
% 2.18/1.02  --clausify_out                          false
% 2.18/1.02  --sig_cnt_out                           false
% 2.18/1.02  --trig_cnt_out                          false
% 2.18/1.02  --trig_cnt_out_tolerance                1.
% 2.18/1.02  --trig_cnt_out_sk_spl                   false
% 2.18/1.02  --abstr_cl_out                          false
% 2.18/1.02  
% 2.18/1.02  ------ Global Options
% 2.18/1.02  
% 2.18/1.02  --schedule                              default
% 2.18/1.02  --add_important_lit                     false
% 2.18/1.02  --prop_solver_per_cl                    1000
% 2.18/1.02  --min_unsat_core                        false
% 2.18/1.02  --soft_assumptions                      false
% 2.18/1.02  --soft_lemma_size                       3
% 2.18/1.02  --prop_impl_unit_size                   0
% 2.18/1.02  --prop_impl_unit                        []
% 2.18/1.02  --share_sel_clauses                     true
% 2.18/1.02  --reset_solvers                         false
% 2.18/1.02  --bc_imp_inh                            [conj_cone]
% 2.18/1.02  --conj_cone_tolerance                   3.
% 2.18/1.02  --extra_neg_conj                        none
% 2.18/1.02  --large_theory_mode                     true
% 2.18/1.02  --prolific_symb_bound                   200
% 2.18/1.02  --lt_threshold                          2000
% 2.18/1.02  --clause_weak_htbl                      true
% 2.18/1.02  --gc_record_bc_elim                     false
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing Options
% 2.18/1.02  
% 2.18/1.02  --preprocessing_flag                    true
% 2.18/1.02  --time_out_prep_mult                    0.1
% 2.18/1.02  --splitting_mode                        input
% 2.18/1.02  --splitting_grd                         true
% 2.18/1.02  --splitting_cvd                         false
% 2.18/1.02  --splitting_cvd_svl                     false
% 2.18/1.02  --splitting_nvd                         32
% 2.18/1.02  --sub_typing                            true
% 2.18/1.02  --prep_gs_sim                           true
% 2.18/1.02  --prep_unflatten                        true
% 2.18/1.02  --prep_res_sim                          true
% 2.18/1.02  --prep_upred                            true
% 2.18/1.02  --prep_sem_filter                       exhaustive
% 2.18/1.02  --prep_sem_filter_out                   false
% 2.18/1.02  --pred_elim                             true
% 2.18/1.02  --res_sim_input                         true
% 2.18/1.02  --eq_ax_congr_red                       true
% 2.18/1.02  --pure_diseq_elim                       true
% 2.18/1.02  --brand_transform                       false
% 2.18/1.02  --non_eq_to_eq                          false
% 2.18/1.02  --prep_def_merge                        true
% 2.18/1.02  --prep_def_merge_prop_impl              false
% 2.18/1.02  --prep_def_merge_mbd                    true
% 2.18/1.02  --prep_def_merge_tr_red                 false
% 2.18/1.02  --prep_def_merge_tr_cl                  false
% 2.18/1.02  --smt_preprocessing                     true
% 2.18/1.02  --smt_ac_axioms                         fast
% 2.18/1.02  --preprocessed_out                      false
% 2.18/1.02  --preprocessed_stats                    false
% 2.18/1.02  
% 2.18/1.02  ------ Abstraction refinement Options
% 2.18/1.02  
% 2.18/1.02  --abstr_ref                             []
% 2.18/1.02  --abstr_ref_prep                        false
% 2.18/1.02  --abstr_ref_until_sat                   false
% 2.18/1.02  --abstr_ref_sig_restrict                funpre
% 2.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.02  --abstr_ref_under                       []
% 2.18/1.02  
% 2.18/1.02  ------ SAT Options
% 2.18/1.02  
% 2.18/1.02  --sat_mode                              false
% 2.18/1.02  --sat_fm_restart_options                ""
% 2.18/1.02  --sat_gr_def                            false
% 2.18/1.02  --sat_epr_types                         true
% 2.18/1.02  --sat_non_cyclic_types                  false
% 2.18/1.02  --sat_finite_models                     false
% 2.18/1.02  --sat_fm_lemmas                         false
% 2.18/1.02  --sat_fm_prep                           false
% 2.18/1.02  --sat_fm_uc_incr                        true
% 2.18/1.02  --sat_out_model                         small
% 2.18/1.02  --sat_out_clauses                       false
% 2.18/1.02  
% 2.18/1.02  ------ QBF Options
% 2.18/1.02  
% 2.18/1.02  --qbf_mode                              false
% 2.18/1.02  --qbf_elim_univ                         false
% 2.18/1.02  --qbf_dom_inst                          none
% 2.18/1.02  --qbf_dom_pre_inst                      false
% 2.18/1.02  --qbf_sk_in                             false
% 2.18/1.02  --qbf_pred_elim                         true
% 2.18/1.02  --qbf_split                             512
% 2.18/1.02  
% 2.18/1.02  ------ BMC1 Options
% 2.18/1.02  
% 2.18/1.02  --bmc1_incremental                      false
% 2.18/1.02  --bmc1_axioms                           reachable_all
% 2.18/1.02  --bmc1_min_bound                        0
% 2.18/1.02  --bmc1_max_bound                        -1
% 2.18/1.02  --bmc1_max_bound_default                -1
% 2.18/1.02  --bmc1_symbol_reachability              true
% 2.18/1.02  --bmc1_property_lemmas                  false
% 2.18/1.02  --bmc1_k_induction                      false
% 2.18/1.02  --bmc1_non_equiv_states                 false
% 2.18/1.02  --bmc1_deadlock                         false
% 2.18/1.02  --bmc1_ucm                              false
% 2.18/1.02  --bmc1_add_unsat_core                   none
% 2.18/1.02  --bmc1_unsat_core_children              false
% 2.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.02  --bmc1_out_stat                         full
% 2.18/1.02  --bmc1_ground_init                      false
% 2.18/1.02  --bmc1_pre_inst_next_state              false
% 2.18/1.02  --bmc1_pre_inst_state                   false
% 2.18/1.02  --bmc1_pre_inst_reach_state             false
% 2.18/1.02  --bmc1_out_unsat_core                   false
% 2.18/1.02  --bmc1_aig_witness_out                  false
% 2.18/1.02  --bmc1_verbose                          false
% 2.18/1.02  --bmc1_dump_clauses_tptp                false
% 2.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.02  --bmc1_dump_file                        -
% 2.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.02  --bmc1_ucm_extend_mode                  1
% 2.18/1.02  --bmc1_ucm_init_mode                    2
% 2.18/1.02  --bmc1_ucm_cone_mode                    none
% 2.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.02  --bmc1_ucm_relax_model                  4
% 2.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.02  --bmc1_ucm_layered_model                none
% 2.18/1.02  --bmc1_ucm_max_lemma_size               10
% 2.18/1.02  
% 2.18/1.02  ------ AIG Options
% 2.18/1.02  
% 2.18/1.02  --aig_mode                              false
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation Options
% 2.18/1.02  
% 2.18/1.02  --instantiation_flag                    true
% 2.18/1.02  --inst_sos_flag                         false
% 2.18/1.02  --inst_sos_phase                        true
% 2.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel_side                     num_symb
% 2.18/1.02  --inst_solver_per_active                1400
% 2.18/1.02  --inst_solver_calls_frac                1.
% 2.18/1.02  --inst_passive_queue_type               priority_queues
% 2.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.02  --inst_passive_queues_freq              [25;2]
% 2.18/1.02  --inst_dismatching                      true
% 2.18/1.02  --inst_eager_unprocessed_to_passive     true
% 2.18/1.02  --inst_prop_sim_given                   true
% 2.18/1.02  --inst_prop_sim_new                     false
% 2.18/1.02  --inst_subs_new                         false
% 2.18/1.02  --inst_eq_res_simp                      false
% 2.18/1.02  --inst_subs_given                       false
% 2.18/1.02  --inst_orphan_elimination               true
% 2.18/1.02  --inst_learning_loop_flag               true
% 2.18/1.02  --inst_learning_start                   3000
% 2.18/1.02  --inst_learning_factor                  2
% 2.18/1.02  --inst_start_prop_sim_after_learn       3
% 2.18/1.02  --inst_sel_renew                        solver
% 2.18/1.02  --inst_lit_activity_flag                true
% 2.18/1.02  --inst_restr_to_given                   false
% 2.18/1.02  --inst_activity_threshold               500
% 2.18/1.02  --inst_out_proof                        true
% 2.18/1.02  
% 2.18/1.02  ------ Resolution Options
% 2.18/1.02  
% 2.18/1.02  --resolution_flag                       true
% 2.18/1.02  --res_lit_sel                           adaptive
% 2.18/1.02  --res_lit_sel_side                      none
% 2.18/1.02  --res_ordering                          kbo
% 2.18/1.02  --res_to_prop_solver                    active
% 2.18/1.02  --res_prop_simpl_new                    false
% 2.18/1.02  --res_prop_simpl_given                  true
% 2.18/1.02  --res_passive_queue_type                priority_queues
% 2.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.02  --res_passive_queues_freq               [15;5]
% 2.18/1.02  --res_forward_subs                      full
% 2.18/1.02  --res_backward_subs                     full
% 2.18/1.02  --res_forward_subs_resolution           true
% 2.18/1.02  --res_backward_subs_resolution          true
% 2.18/1.02  --res_orphan_elimination                true
% 2.18/1.02  --res_time_limit                        2.
% 2.18/1.02  --res_out_proof                         true
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Options
% 2.18/1.02  
% 2.18/1.02  --superposition_flag                    true
% 2.18/1.02  --sup_passive_queue_type                priority_queues
% 2.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.02  --demod_completeness_check              fast
% 2.18/1.02  --demod_use_ground                      true
% 2.18/1.02  --sup_to_prop_solver                    passive
% 2.18/1.02  --sup_prop_simpl_new                    true
% 2.18/1.02  --sup_prop_simpl_given                  true
% 2.18/1.02  --sup_fun_splitting                     false
% 2.18/1.02  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  ------ Parsing...
% 2.18/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.02  ------ Proving...
% 2.18/1.02  ------ Problem Properties 
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  clauses                                 23
% 2.18/1.02  conjectures                             4
% 2.18/1.02  EPR                                     3
% 2.18/1.02  Horn                                    21
% 2.18/1.02  unary                                   5
% 2.18/1.02  binary                                  7
% 2.18/1.02  lits                                    60
% 2.18/1.02  lits eq                                 13
% 2.18/1.02  fd_pure                                 0
% 2.18/1.02  fd_pseudo                               0
% 2.18/1.02  fd_cond                                 0
% 2.18/1.02  fd_pseudo_cond                          0
% 2.18/1.02  AC symbols                              0
% 2.18/1.02  
% 2.18/1.02  ------ Schedule dynamic 5 is on 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ 
% 2.18/1.02  Current options:
% 2.18/1.02  ------ 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options
% 2.18/1.02  
% 2.18/1.02  --out_options                           all
% 2.18/1.02  --tptp_safe_out                         true
% 2.18/1.02  --problem_path                          ""
% 2.18/1.02  --include_path                          ""
% 2.18/1.02  --clausifier                            res/vclausify_rel
% 2.18/1.02  --clausifier_options                    --mode clausify
% 2.18/1.02  --stdin                                 false
% 2.18/1.02  --stats_out                             all
% 2.18/1.02  
% 2.18/1.02  ------ General Options
% 2.18/1.02  
% 2.18/1.02  --fof                                   false
% 2.18/1.02  --time_out_real                         305.
% 2.18/1.02  --time_out_virtual                      -1.
% 2.18/1.02  --symbol_type_check                     false
% 2.18/1.02  --clausify_out                          false
% 2.18/1.02  --sig_cnt_out                           false
% 2.18/1.02  --trig_cnt_out                          false
% 2.18/1.02  --trig_cnt_out_tolerance                1.
% 2.18/1.02  --trig_cnt_out_sk_spl                   false
% 2.18/1.02  --abstr_cl_out                          false
% 2.18/1.02  
% 2.18/1.02  ------ Global Options
% 2.18/1.02  
% 2.18/1.02  --schedule                              default
% 2.18/1.02  --add_important_lit                     false
% 2.18/1.02  --prop_solver_per_cl                    1000
% 2.18/1.02  --min_unsat_core                        false
% 2.18/1.02  --soft_assumptions                      false
% 2.18/1.02  --soft_lemma_size                       3
% 2.18/1.02  --prop_impl_unit_size                   0
% 2.18/1.02  --prop_impl_unit                        []
% 2.18/1.02  --share_sel_clauses                     true
% 2.18/1.02  --reset_solvers                         false
% 2.18/1.02  --bc_imp_inh                            [conj_cone]
% 2.18/1.02  --conj_cone_tolerance                   3.
% 2.18/1.02  --extra_neg_conj                        none
% 2.18/1.02  --large_theory_mode                     true
% 2.18/1.02  --prolific_symb_bound                   200
% 2.18/1.02  --lt_threshold                          2000
% 2.18/1.02  --clause_weak_htbl                      true
% 2.18/1.02  --gc_record_bc_elim                     false
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing Options
% 2.18/1.02  
% 2.18/1.02  --preprocessing_flag                    true
% 2.18/1.02  --time_out_prep_mult                    0.1
% 2.18/1.02  --splitting_mode                        input
% 2.18/1.02  --splitting_grd                         true
% 2.18/1.02  --splitting_cvd                         false
% 2.18/1.02  --splitting_cvd_svl                     false
% 2.18/1.02  --splitting_nvd                         32
% 2.18/1.02  --sub_typing                            true
% 2.18/1.02  --prep_gs_sim                           true
% 2.18/1.02  --prep_unflatten                        true
% 2.18/1.02  --prep_res_sim                          true
% 2.18/1.02  --prep_upred                            true
% 2.18/1.02  --prep_sem_filter                       exhaustive
% 2.18/1.02  --prep_sem_filter_out                   false
% 2.18/1.02  --pred_elim                             true
% 2.18/1.02  --res_sim_input                         true
% 2.18/1.02  --eq_ax_congr_red                       true
% 2.18/1.02  --pure_diseq_elim                       true
% 2.18/1.02  --brand_transform                       false
% 2.18/1.02  --non_eq_to_eq                          false
% 2.18/1.02  --prep_def_merge                        true
% 2.18/1.02  --prep_def_merge_prop_impl              false
% 2.18/1.02  --prep_def_merge_mbd                    true
% 2.18/1.02  --prep_def_merge_tr_red                 false
% 2.18/1.02  --prep_def_merge_tr_cl                  false
% 2.18/1.02  --smt_preprocessing                     true
% 2.18/1.02  --smt_ac_axioms                         fast
% 2.18/1.02  --preprocessed_out                      false
% 2.18/1.02  --preprocessed_stats                    false
% 2.18/1.02  
% 2.18/1.02  ------ Abstraction refinement Options
% 2.18/1.02  
% 2.18/1.02  --abstr_ref                             []
% 2.18/1.02  --abstr_ref_prep                        false
% 2.18/1.02  --abstr_ref_until_sat                   false
% 2.18/1.02  --abstr_ref_sig_restrict                funpre
% 2.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.02  --abstr_ref_under                       []
% 2.18/1.02  
% 2.18/1.02  ------ SAT Options
% 2.18/1.02  
% 2.18/1.02  --sat_mode                              false
% 2.18/1.02  --sat_fm_restart_options                ""
% 2.18/1.02  --sat_gr_def                            false
% 2.18/1.02  --sat_epr_types                         true
% 2.18/1.02  --sat_non_cyclic_types                  false
% 2.18/1.02  --sat_finite_models                     false
% 2.18/1.02  --sat_fm_lemmas                         false
% 2.18/1.02  --sat_fm_prep                           false
% 2.18/1.02  --sat_fm_uc_incr                        true
% 2.18/1.02  --sat_out_model                         small
% 2.18/1.02  --sat_out_clauses                       false
% 2.18/1.02  
% 2.18/1.02  ------ QBF Options
% 2.18/1.02  
% 2.18/1.02  --qbf_mode                              false
% 2.18/1.02  --qbf_elim_univ                         false
% 2.18/1.02  --qbf_dom_inst                          none
% 2.18/1.02  --qbf_dom_pre_inst                      false
% 2.18/1.02  --qbf_sk_in                             false
% 2.18/1.02  --qbf_pred_elim                         true
% 2.18/1.02  --qbf_split                             512
% 2.18/1.02  
% 2.18/1.02  ------ BMC1 Options
% 2.18/1.02  
% 2.18/1.02  --bmc1_incremental                      false
% 2.18/1.02  --bmc1_axioms                           reachable_all
% 2.18/1.02  --bmc1_min_bound                        0
% 2.18/1.02  --bmc1_max_bound                        -1
% 2.18/1.02  --bmc1_max_bound_default                -1
% 2.18/1.02  --bmc1_symbol_reachability              true
% 2.18/1.02  --bmc1_property_lemmas                  false
% 2.18/1.02  --bmc1_k_induction                      false
% 2.18/1.02  --bmc1_non_equiv_states                 false
% 2.18/1.02  --bmc1_deadlock                         false
% 2.18/1.02  --bmc1_ucm                              false
% 2.18/1.02  --bmc1_add_unsat_core                   none
% 2.18/1.02  --bmc1_unsat_core_children              false
% 2.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.02  --bmc1_out_stat                         full
% 2.18/1.02  --bmc1_ground_init                      false
% 2.18/1.02  --bmc1_pre_inst_next_state              false
% 2.18/1.02  --bmc1_pre_inst_state                   false
% 2.18/1.02  --bmc1_pre_inst_reach_state             false
% 2.18/1.02  --bmc1_out_unsat_core                   false
% 2.18/1.02  --bmc1_aig_witness_out                  false
% 2.18/1.02  --bmc1_verbose                          false
% 2.18/1.02  --bmc1_dump_clauses_tptp                false
% 2.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.02  --bmc1_dump_file                        -
% 2.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.02  --bmc1_ucm_extend_mode                  1
% 2.18/1.02  --bmc1_ucm_init_mode                    2
% 2.18/1.02  --bmc1_ucm_cone_mode                    none
% 2.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.02  --bmc1_ucm_relax_model                  4
% 2.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.02  --bmc1_ucm_layered_model                none
% 2.18/1.02  --bmc1_ucm_max_lemma_size               10
% 2.18/1.02  
% 2.18/1.02  ------ AIG Options
% 2.18/1.02  
% 2.18/1.02  --aig_mode                              false
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation Options
% 2.18/1.02  
% 2.18/1.02  --instantiation_flag                    true
% 2.18/1.02  --inst_sos_flag                         false
% 2.18/1.02  --inst_sos_phase                        true
% 2.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel_side                     none
% 2.18/1.02  --inst_solver_per_active                1400
% 2.18/1.02  --inst_solver_calls_frac                1.
% 2.18/1.02  --inst_passive_queue_type               priority_queues
% 2.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.02  --inst_passive_queues_freq              [25;2]
% 2.18/1.02  --inst_dismatching                      true
% 2.18/1.02  --inst_eager_unprocessed_to_passive     true
% 2.18/1.02  --inst_prop_sim_given                   true
% 2.18/1.02  --inst_prop_sim_new                     false
% 2.18/1.02  --inst_subs_new                         false
% 2.18/1.02  --inst_eq_res_simp                      false
% 2.18/1.02  --inst_subs_given                       false
% 2.18/1.02  --inst_orphan_elimination               true
% 2.18/1.02  --inst_learning_loop_flag               true
% 2.18/1.02  --inst_learning_start                   3000
% 2.18/1.02  --inst_learning_factor                  2
% 2.18/1.02  --inst_start_prop_sim_after_learn       3
% 2.18/1.02  --inst_sel_renew                        solver
% 2.18/1.02  --inst_lit_activity_flag                true
% 2.18/1.02  --inst_restr_to_given                   false
% 2.18/1.02  --inst_activity_threshold               500
% 2.18/1.02  --inst_out_proof                        true
% 2.18/1.02  
% 2.18/1.02  ------ Resolution Options
% 2.18/1.02  
% 2.18/1.02  --resolution_flag                       false
% 2.18/1.02  --res_lit_sel                           adaptive
% 2.18/1.02  --res_lit_sel_side                      none
% 2.18/1.02  --res_ordering                          kbo
% 2.18/1.02  --res_to_prop_solver                    active
% 2.18/1.02  --res_prop_simpl_new                    false
% 2.18/1.02  --res_prop_simpl_given                  true
% 2.18/1.02  --res_passive_queue_type                priority_queues
% 2.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.02  --res_passive_queues_freq               [15;5]
% 2.18/1.02  --res_forward_subs                      full
% 2.18/1.02  --res_backward_subs                     full
% 2.18/1.02  --res_forward_subs_resolution           true
% 2.18/1.02  --res_backward_subs_resolution          true
% 2.18/1.02  --res_orphan_elimination                true
% 2.18/1.02  --res_time_limit                        2.
% 2.18/1.02  --res_out_proof                         true
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Options
% 2.18/1.02  
% 2.18/1.02  --superposition_flag                    true
% 2.18/1.02  --sup_passive_queue_type                priority_queues
% 2.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.02  --demod_completeness_check              fast
% 2.18/1.02  --demod_use_ground                      true
% 2.18/1.02  --sup_to_prop_solver                    passive
% 2.18/1.02  --sup_prop_simpl_new                    true
% 2.18/1.02  --sup_prop_simpl_given                  true
% 2.18/1.02  --sup_fun_splitting                     false
% 2.18/1.02  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ Proving...
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS status Theorem for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  fof(f5,axiom,(
% 2.18/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f18,plain,(
% 2.18/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.02    inference(ennf_transformation,[],[f5])).
% 2.18/1.02  
% 2.18/1.02  fof(f42,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f18])).
% 2.18/1.02  
% 2.18/1.02  fof(f7,axiom,(
% 2.18/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f21,plain,(
% 2.18/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/1.02    inference(ennf_transformation,[],[f7])).
% 2.18/1.02  
% 2.18/1.02  fof(f22,plain,(
% 2.18/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.02    inference(flattening,[],[f21])).
% 2.18/1.02  
% 2.18/1.02  fof(f31,plain,(
% 2.18/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.02    inference(nnf_transformation,[],[f22])).
% 2.18/1.02  
% 2.18/1.02  fof(f46,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f31])).
% 2.18/1.02  
% 2.18/1.02  fof(f11,conjecture,(
% 2.18/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)))))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f12,negated_conjecture,(
% 2.18/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)))))))),
% 2.18/1.02    inference(negated_conjecture,[],[f11])).
% 2.18/1.02  
% 2.18/1.02  fof(f29,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f12])).
% 2.18/1.02  
% 2.18/1.02  fof(f30,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.18/1.02    inference(flattening,[],[f29])).
% 2.18/1.02  
% 2.18/1.02  fof(f36,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f35,plain,(
% 2.18/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f34,plain,(
% 2.18/1.02    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) != k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f33,plain,(
% 2.18/1.02    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) != k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f32,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) != k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f37,plain,(
% 2.18/1.02    ((((k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f36,f35,f34,f33,f32])).
% 2.18/1.02  
% 2.18/1.02  fof(f59,plain,(
% 2.18/1.02    v1_partfun1(sK4,sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f57,plain,(
% 2.18/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f2,axiom,(
% 2.18/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f15,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f2])).
% 2.18/1.02  
% 2.18/1.02  fof(f39,plain,(
% 2.18/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f15])).
% 2.18/1.02  
% 2.18/1.02  fof(f3,axiom,(
% 2.18/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f40,plain,(
% 2.18/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f3])).
% 2.18/1.02  
% 2.18/1.02  fof(f4,axiom,(
% 2.18/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f16,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/1.02    inference(ennf_transformation,[],[f4])).
% 2.18/1.02  
% 2.18/1.02  fof(f17,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.02    inference(flattening,[],[f16])).
% 2.18/1.02  
% 2.18/1.02  fof(f41,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f17])).
% 2.18/1.02  
% 2.18/1.02  fof(f53,plain,(
% 2.18/1.02    v1_funct_1(sK3)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f55,plain,(
% 2.18/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f8,axiom,(
% 2.18/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f23,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/1.02    inference(ennf_transformation,[],[f8])).
% 2.18/1.02  
% 2.18/1.02  fof(f24,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.02    inference(flattening,[],[f23])).
% 2.18/1.02  
% 2.18/1.02  fof(f48,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f24])).
% 2.18/1.02  
% 2.18/1.02  fof(f56,plain,(
% 2.18/1.02    v1_funct_1(sK4)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f58,plain,(
% 2.18/1.02    m1_subset_1(sK5,sK1)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f6,axiom,(
% 2.18/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f19,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f6])).
% 2.18/1.02  
% 2.18/1.02  fof(f20,plain,(
% 2.18/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.18/1.02    inference(flattening,[],[f19])).
% 2.18/1.02  
% 2.18/1.02  fof(f45,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f20])).
% 2.18/1.02  
% 2.18/1.02  fof(f54,plain,(
% 2.18/1.02    v1_funct_2(sK3,sK1,sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f51,plain,(
% 2.18/1.02    ~v1_xboole_0(sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f1,axiom,(
% 2.18/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f13,plain,(
% 2.18/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f1])).
% 2.18/1.02  
% 2.18/1.02  fof(f14,plain,(
% 2.18/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.18/1.02    inference(flattening,[],[f13])).
% 2.18/1.02  
% 2.18/1.02  fof(f38,plain,(
% 2.18/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f14])).
% 2.18/1.02  
% 2.18/1.02  fof(f52,plain,(
% 2.18/1.02    ~v1_xboole_0(sK1)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  fof(f43,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f18])).
% 2.18/1.02  
% 2.18/1.02  fof(f10,axiom,(
% 2.18/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)))))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f27,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f10])).
% 2.18/1.02  
% 2.18/1.02  fof(f28,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.18/1.02    inference(flattening,[],[f27])).
% 2.18/1.02  
% 2.18/1.02  fof(f50,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  fof(f9,axiom,(
% 2.18/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f25,plain,(
% 2.18/1.02    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.18/1.02    inference(ennf_transformation,[],[f9])).
% 2.18/1.02  
% 2.18/1.02  fof(f26,plain,(
% 2.18/1.02    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.18/1.02    inference(flattening,[],[f25])).
% 2.18/1.02  
% 2.18/1.02  fof(f49,plain,(
% 2.18/1.02    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f26])).
% 2.18/1.02  
% 2.18/1.02  fof(f60,plain,(
% 2.18/1.02    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 2.18/1.02    inference(cnf_transformation,[],[f37])).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5,plain,
% 2.18/1.02      ( v4_relat_1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.18/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_9,plain,
% 2.18/1.02      ( ~ v1_partfun1(X0,X1)
% 2.18/1.02      | ~ v4_relat_1(X0,X1)
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | k1_relat_1(X0) = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_14,negated_conjecture,
% 2.18/1.02      ( v1_partfun1(sK4,sK0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_651,plain,
% 2.18/1.02      ( ~ v4_relat_1(X0,X1)
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | k1_relat_1(X0) = X1
% 2.18/1.02      | sK0 != X1
% 2.18/1.02      | sK4 != X0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_652,plain,
% 2.18/1.02      ( ~ v4_relat_1(sK4,sK0)
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_651]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_768,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k1_relat_1(sK4) = sK0
% 2.18/1.02      | sK0 != X1
% 2.18/1.02      | sK4 != X0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_652]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_769,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_768]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1060,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_769]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1077,plain,
% 2.18/1.02      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 2.18/1.02      inference(splitting,
% 2.18/1.02                [splitting(split),new_symbols(definition,[])],
% 2.18/1.02                [c_1060]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1527,plain,
% 2.18/1.02      ( k1_relat_1(sK4) = sK0
% 2.18/1.02      | v1_relat_1(sK4) != iProver_top
% 2.18/1.02      | sP0_iProver_split = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1143,plain,
% 2.18/1.02      ( k1_relat_1(sK4) = sK0
% 2.18/1.02      | v1_relat_1(sK4) != iProver_top
% 2.18/1.02      | sP0_iProver_split = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_16,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.18/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1070,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1517,plain,
% 2.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.02      | ~ v1_relat_1(X1)
% 2.18/1.02      | v1_relat_1(X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1075,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.18/1.02      | ~ v1_relat_1(X1_50)
% 2.18/1.02      | v1_relat_1(X0_50) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1513,plain,
% 2.18/1.02      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 2.18/1.02      | v1_relat_1(X1_50) != iProver_top
% 2.18/1.02      | v1_relat_1(X0_50) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1827,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.18/1.02      | v1_relat_1(sK4) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1517,c_1513]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1074,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1857,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1074]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1858,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1857]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1076,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 2.18/1.02      | ~ sP0_iProver_split ),
% 2.18/1.02      inference(splitting,
% 2.18/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.18/1.02                [c_1060]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1528,plain,
% 2.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 2.18/1.02      | sP0_iProver_split != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2346,plain,
% 2.18/1.02      ( sP0_iProver_split != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1517,c_1528]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2681,plain,
% 2.18/1.02      ( k1_relat_1(sK4) = sK0 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_1527,c_1143,c_1827,c_1858,c_2346]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3,plain,
% 2.18/1.02      ( ~ v5_relat_1(X0,X1)
% 2.18/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.18/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | ~ v1_relat_1(X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_20,negated_conjecture,
% 2.18/1.02      ( v1_funct_1(sK3) ),
% 2.18/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_514,plain,
% 2.18/1.02      ( ~ v5_relat_1(X0,X1)
% 2.18/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.18/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | sK3 != X0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_515,plain,
% 2.18/1.02      ( ~ v5_relat_1(sK3,X0)
% 2.18/1.02      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.18/1.02      | r2_hidden(k1_funct_1(sK3,X1),X0)
% 2.18/1.02      | ~ v1_relat_1(sK3) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_514]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1061,plain,
% 2.18/1.02      ( ~ v5_relat_1(sK3,X0_51)
% 2.18/1.02      | ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.02      | r2_hidden(k1_funct_1(sK3,X0_50),X0_51)
% 2.18/1.02      | ~ v1_relat_1(sK3) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_515]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1526,plain,
% 2.18/1.02      ( v5_relat_1(sK3,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.02      | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
% 2.18/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1140,plain,
% 2.18/1.02      ( v5_relat_1(sK3,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.02      | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
% 2.18/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_18,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.18/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1069,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1518,plain,
% 2.18/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1828,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.18/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1518,c_1513]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1860,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1074]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1861,plain,
% 2.18/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2066,plain,
% 2.18/1.02      ( r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.02      | v5_relat_1(sK3,X0_51) != iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_1526,c_1140,c_1828,c_1861]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2067,plain,
% 2.18/1.02      ( v5_relat_1(sK3,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.02      | r2_hidden(k1_funct_1(sK3,X0_50),X0_51) = iProver_top ),
% 2.18/1.02      inference(renaming,[status(thm)],[c_2066]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_10,plain,
% 2.18/1.02      ( ~ v5_relat_1(X0,X1)
% 2.18/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.18/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_17,negated_conjecture,
% 2.18/1.02      ( v1_funct_1(sK4) ),
% 2.18/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_442,plain,
% 2.18/1.02      ( ~ v5_relat_1(X0,X1)
% 2.18/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2)
% 2.18/1.02      | sK4 != X0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_443,plain,
% 2.18/1.02      ( ~ v5_relat_1(sK4,X0)
% 2.18/1.02      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_442]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1064,plain,
% 2.18/1.02      ( ~ v5_relat_1(sK4,X0_51)
% 2.18/1.02      | ~ r2_hidden(X0_50,k1_relat_1(sK4))
% 2.18/1.02      | ~ v1_relat_1(sK4)
% 2.18/1.02      | k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_443]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1523,plain,
% 2.18/1.02      ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.18/1.02      | v5_relat_1(sK4,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 2.18/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1131,plain,
% 2.18/1.02      ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.18/1.02      | v5_relat_1(sK4,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 2.18/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2076,plain,
% 2.18/1.02      ( r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 2.18/1.02      | v5_relat_1(sK4,X0_51) != iProver_top
% 2.18/1.02      | k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_1523,c_1131,c_1827,c_1858]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2077,plain,
% 2.18/1.02      ( k7_partfun1(X0_51,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.18/1.02      | v5_relat_1(sK4,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top ),
% 2.18/1.02      inference(renaming,[status(thm)],[c_2076]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2085,plain,
% 2.18/1.02      ( k7_partfun1(X0_51,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
% 2.18/1.02      | v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top
% 2.18/1.02      | v5_relat_1(sK4,X0_51) != iProver_top
% 2.18/1.02      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_2067,c_2077]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_29,plain,
% 2.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_15,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK5,sK1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_30,plain,
% 2.18/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_6,plain,
% 2.18/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.02      | v1_partfun1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | v1_xboole_0(X2) ),
% 2.18/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_19,negated_conjecture,
% 2.18/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_369,plain,
% 2.18/1.02      ( v1_partfun1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | v1_xboole_0(X2)
% 2.18/1.02      | sK3 != X0
% 2.18/1.02      | sK0 != X2
% 2.18/1.02      | sK1 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_370,plain,
% 2.18/1.02      ( v1_partfun1(sK3,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.18/1.02      | ~ v1_funct_1(sK3)
% 2.18/1.02      | v1_xboole_0(sK0) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_369]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_22,negated_conjecture,
% 2.18/1.02      ( ~ v1_xboole_0(sK0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_372,plain,
% 2.18/1.02      ( v1_partfun1(sK3,sK1) ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_370,c_22,c_20,c_18]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_664,plain,
% 2.18/1.02      ( ~ v4_relat_1(X0,X1)
% 2.18/1.02      | ~ v1_relat_1(X0)
% 2.18/1.02      | k1_relat_1(X0) = X1
% 2.18/1.02      | sK3 != X0
% 2.18/1.02      | sK1 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_372]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_665,plain,
% 2.18/1.02      ( ~ v4_relat_1(sK3,sK1)
% 2.18/1.02      | ~ v1_relat_1(sK3)
% 2.18/1.02      | k1_relat_1(sK3) = sK1 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_664]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_783,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_relat_1(sK3)
% 2.18/1.02      | k1_relat_1(sK3) = sK1
% 2.18/1.02      | sK3 != X0
% 2.18/1.02      | sK1 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_665]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_784,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 2.18/1.02      | ~ v1_relat_1(sK3)
% 2.18/1.02      | k1_relat_1(sK3) = sK1 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_783]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_786,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.18/1.02      | ~ v1_relat_1(sK3)
% 2.18/1.02      | k1_relat_1(sK3) = sK1 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_784]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_788,plain,
% 2.18/1.02      ( ~ v1_relat_1(sK3) | k1_relat_1(sK3) = sK1 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_784,c_18,c_786]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1059,plain,
% 2.18/1.02      ( ~ v1_relat_1(sK3) | k1_relat_1(sK3) = sK1 ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_788]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_0,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_21,negated_conjecture,
% 2.18/1.02      ( ~ v1_xboole_0(sK1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_391,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK1 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_392,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_391]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1067,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0_50,sK1) | r2_hidden(X0_50,sK1) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_392]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1703,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1067]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1704,plain,
% 2.18/1.02      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.18/1.02      | r2_hidden(sK5,sK1) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_4,plain,
% 2.18/1.02      ( v5_relat_1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.18/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1073,plain,
% 2.18/1.02      ( v5_relat_1(X0_50,X0_51)
% 2.18/1.02      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1731,plain,
% 2.18/1.02      ( v5_relat_1(sK4,sK2)
% 2.18/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1073]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1732,plain,
% 2.18/1.02      ( v5_relat_1(sK4,sK2) = iProver_top
% 2.18/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1731]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1838,plain,
% 2.18/1.02      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 2.18/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1828]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1086,plain,
% 2.18/1.02      ( ~ r2_hidden(X0_50,X0_51)
% 2.18/1.02      | r2_hidden(X1_50,X1_51)
% 2.18/1.02      | X1_51 != X0_51
% 2.18/1.02      | X1_50 != X0_50 ),
% 2.18/1.02      theory(equality) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1765,plain,
% 2.18/1.02      ( r2_hidden(X0_50,X0_51)
% 2.18/1.02      | ~ r2_hidden(sK5,sK1)
% 2.18/1.02      | X0_51 != sK1
% 2.18/1.02      | X0_50 != sK5 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1086]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1980,plain,
% 2.18/1.02      ( r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.02      | ~ r2_hidden(sK5,sK1)
% 2.18/1.02      | k1_relat_1(sK3) != sK1
% 2.18/1.02      | X0_50 != sK5 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1765]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2137,plain,
% 2.18/1.02      ( r2_hidden(sK5,k1_relat_1(sK3))
% 2.18/1.02      | ~ r2_hidden(sK5,sK1)
% 2.18/1.02      | k1_relat_1(sK3) != sK1
% 2.18/1.02      | sK5 != sK5 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1980]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2139,plain,
% 2.18/1.02      ( k1_relat_1(sK3) != sK1
% 2.18/1.02      | sK5 != sK5
% 2.18/1.02      | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.18/1.02      | r2_hidden(sK5,sK1) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_2137]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1082,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2138,plain,
% 2.18/1.02      ( sK5 = sK5 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1082]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1071,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK5,sK1) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1516,plain,
% 2.18/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_12,plain,
% 2.18/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.02      | ~ v1_partfun1(X3,X2)
% 2.18/1.02      | ~ m1_subset_1(X4,X1)
% 2.18/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_funct_1(X3)
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | v1_xboole_0(X1)
% 2.18/1.02      | v1_xboole_0(X2)
% 2.18/1.02      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 2.18/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_324,plain,
% 2.18/1.02      ( ~ v1_partfun1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X2,X3)
% 2.18/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 2.18/1.02      | ~ v1_funct_1(X4)
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | v1_xboole_0(X3)
% 2.18/1.02      | v1_xboole_0(X1)
% 2.18/1.02      | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
% 2.18/1.02      | sK3 != X4
% 2.18/1.02      | sK0 != X1
% 2.18/1.02      | sK1 != X3 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_325,plain,
% 2.18/1.02      ( ~ v1_partfun1(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | ~ m1_subset_1(X2,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | ~ v1_funct_1(sK3)
% 2.18/1.02      | v1_xboole_0(sK0)
% 2.18/1.02      | v1_xboole_0(sK1)
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_324]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_329,plain,
% 2.18/1.02      ( ~ v1_funct_1(X0)
% 2.18/1.02      | ~ v1_partfun1(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | ~ m1_subset_1(X2,sK1)
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_325,c_22,c_21,c_20,c_18]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_330,plain,
% 2.18/1.02      ( ~ v1_partfun1(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | ~ m1_subset_1(X2,sK1)
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.18/1.02      inference(renaming,[status(thm)],[c_329]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_421,plain,
% 2.18/1.02      ( ~ v1_partfun1(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | ~ m1_subset_1(X2,sK1)
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))
% 2.18/1.02      | sK4 != X0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_330,c_17]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_422,plain,
% 2.18/1.02      ( ~ v1_partfun1(sK4,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_421]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_426,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.18/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_422,c_14]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1065,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0_50,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 2.18/1.02      | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_426]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1522,plain,
% 2.18/1.02      ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.18/1.02      | m1_subset_1(X0_50,sK1) != iProver_top
% 2.18/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1065]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2189,plain,
% 2.18/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.18/1.02      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1517,c_1522]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2254,plain,
% 2.18/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1516,c_2189]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_11,plain,
% 2.18/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.02      | ~ m1_subset_1(X3,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.02      | ~ v1_funct_1(X0)
% 2.18/1.02      | v1_xboole_0(X1)
% 2.18/1.02      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.18/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_351,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.18/1.02      | ~ v1_funct_1(X2)
% 2.18/1.02      | v1_xboole_0(X1)
% 2.18/1.02      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.18/1.02      | sK3 != X2
% 2.18/1.02      | sK0 != X3
% 2.18/1.02      | sK1 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_352,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,sK1)
% 2.18/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.18/1.02      | ~ v1_funct_1(sK3)
% 2.18/1.02      | v1_xboole_0(sK1)
% 2.18/1.02      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_351]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_356,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,sK1)
% 2.18/1.02      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_352,c_21,c_20,c_18]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1068,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0_50,sK1)
% 2.18/1.02      | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
% 2.18/1.02      inference(subtyping,[status(esa)],[c_356]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1519,plain,
% 2.18/1.02      ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
% 2.18/1.02      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1776,plain,
% 2.18/1.02      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1516,c_1519]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2255,plain,
% 2.18/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.18/1.03      inference(light_normalisation,[status(thm)],[c_2254,c_1776]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_13,negated_conjecture,
% 2.18/1.03      ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.18/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_1072,negated_conjecture,
% 2.18/1.03      ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.18/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_1901,plain,
% 2.18/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.18/1.03      inference(demodulation,[status(thm)],[c_1776,c_1072]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2257,plain,
% 2.18/1.03      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.18/1.03      inference(demodulation,[status(thm)],[c_2255,c_1901]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2351,plain,
% 2.18/1.03      ( ~ v5_relat_1(sK3,X0_51)
% 2.18/1.03      | r2_hidden(k1_funct_1(sK3,sK5),X0_51)
% 2.18/1.03      | ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.18/1.03      | ~ v1_relat_1(sK3) ),
% 2.18/1.03      inference(instantiation,[status(thm)],[c_1061]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2384,plain,
% 2.18/1.03      ( ~ v5_relat_1(sK3,k1_relat_1(sK4))
% 2.18/1.03      | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
% 2.18/1.03      | ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.18/1.03      | ~ v1_relat_1(sK3) ),
% 2.18/1.03      inference(instantiation,[status(thm)],[c_2351]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2386,plain,
% 2.18/1.03      ( v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top
% 2.18/1.03      | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) = iProver_top
% 2.18/1.03      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.18/1.03      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.03      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_1893,plain,
% 2.18/1.03      ( ~ v5_relat_1(sK4,sK2)
% 2.18/1.03      | ~ r2_hidden(X0_50,k1_relat_1(sK4))
% 2.18/1.03      | ~ v1_relat_1(sK4)
% 2.18/1.03      | k7_partfun1(sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50) ),
% 2.18/1.03      inference(instantiation,[status(thm)],[c_1064]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2385,plain,
% 2.18/1.03      ( ~ v5_relat_1(sK4,sK2)
% 2.18/1.03      | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
% 2.18/1.03      | ~ v1_relat_1(sK4)
% 2.18/1.03      | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.18/1.03      inference(instantiation,[status(thm)],[c_1893]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2388,plain,
% 2.18/1.03      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.18/1.03      | v5_relat_1(sK4,sK2) != iProver_top
% 2.18/1.03      | r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) != iProver_top
% 2.18/1.03      | v1_relat_1(sK4) != iProver_top ),
% 2.18/1.03      inference(predicate_to_equality,[status(thm)],[c_2385]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2426,plain,
% 2.18/1.03      ( v5_relat_1(sK3,k1_relat_1(sK4)) != iProver_top ),
% 2.18/1.03      inference(global_propositional_subsumption,
% 2.18/1.03                [status(thm)],
% 2.18/1.03                [c_2085,c_29,c_30,c_1059,c_1704,c_1732,c_1827,c_1828,
% 2.18/1.03                 c_1838,c_1858,c_1860,c_1861,c_2139,c_2138,c_2257,c_2386,
% 2.18/1.03                 c_2388]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_2687,plain,
% 2.18/1.03      ( v5_relat_1(sK3,sK0) != iProver_top ),
% 2.18/1.03      inference(demodulation,[status(thm)],[c_2681,c_2426]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_1734,plain,
% 2.18/1.03      ( v5_relat_1(sK3,sK0)
% 2.18/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.18/1.03      inference(instantiation,[status(thm)],[c_1073]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_1735,plain,
% 2.18/1.03      ( v5_relat_1(sK3,sK0) = iProver_top
% 2.18/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1734]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(c_27,plain,
% 2.18/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.18/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.18/1.03  
% 2.18/1.03  cnf(contradiction,plain,
% 2.18/1.03      ( $false ),
% 2.18/1.03      inference(minisat,[status(thm)],[c_2687,c_1735,c_27]) ).
% 2.18/1.03  
% 2.18/1.03  
% 2.18/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.03  
% 2.18/1.03  ------                               Statistics
% 2.18/1.03  
% 2.18/1.03  ------ General
% 2.18/1.03  
% 2.18/1.03  abstr_ref_over_cycles:                  0
% 2.18/1.03  abstr_ref_under_cycles:                 0
% 2.18/1.03  gc_basic_clause_elim:                   0
% 2.18/1.03  forced_gc_time:                         0
% 2.18/1.03  parsing_time:                           0.012
% 2.18/1.03  unif_index_cands_time:                  0.
% 2.18/1.03  unif_index_add_time:                    0.
% 2.18/1.03  orderings_time:                         0.
% 2.18/1.03  out_proof_time:                         0.028
% 2.18/1.03  total_time:                             0.16
% 2.18/1.03  num_of_symbols:                         58
% 2.18/1.03  num_of_terms:                           2317
% 2.18/1.03  
% 2.18/1.03  ------ Preprocessing
% 2.18/1.03  
% 2.18/1.03  num_of_splits:                          3
% 2.18/1.03  num_of_split_atoms:                     3
% 2.18/1.03  num_of_reused_defs:                     0
% 2.18/1.03  num_eq_ax_congr_red:                    7
% 2.18/1.03  num_of_sem_filtered_clauses:            1
% 2.18/1.03  num_of_subtypes:                        2
% 2.18/1.03  monotx_restored_types:                  0
% 2.18/1.03  sat_num_of_epr_types:                   0
% 2.18/1.03  sat_num_of_non_cyclic_types:            0
% 2.18/1.03  sat_guarded_non_collapsed_types:        0
% 2.18/1.03  num_pure_diseq_elim:                    0
% 2.18/1.03  simp_replaced_by:                       0
% 2.18/1.03  res_preprocessed:                       119
% 2.18/1.03  prep_upred:                             0
% 2.18/1.03  prep_unflattend:                        48
% 2.18/1.03  smt_new_axioms:                         0
% 2.18/1.03  pred_elim_cands:                        4
% 2.18/1.03  pred_elim:                              5
% 2.18/1.03  pred_elim_cl:                           2
% 2.18/1.03  pred_elim_cycles:                       10
% 2.18/1.03  merged_defs:                            0
% 2.18/1.03  merged_defs_ncl:                        0
% 2.18/1.03  bin_hyper_res:                          0
% 2.18/1.03  prep_cycles:                            4
% 2.18/1.03  pred_elim_time:                         0.022
% 2.18/1.03  splitting_time:                         0.
% 2.18/1.03  sem_filter_time:                        0.
% 2.18/1.03  monotx_time:                            0.
% 2.18/1.03  subtype_inf_time:                       0.
% 2.18/1.03  
% 2.18/1.03  ------ Problem properties
% 2.18/1.03  
% 2.18/1.03  clauses:                                23
% 2.18/1.03  conjectures:                            4
% 2.18/1.03  epr:                                    3
% 2.18/1.03  horn:                                   21
% 2.18/1.03  ground:                                 7
% 2.18/1.03  unary:                                  5
% 2.18/1.03  binary:                                 7
% 2.18/1.03  lits:                                   60
% 2.18/1.03  lits_eq:                                13
% 2.18/1.03  fd_pure:                                0
% 2.18/1.03  fd_pseudo:                              0
% 2.18/1.03  fd_cond:                                0
% 2.18/1.03  fd_pseudo_cond:                         0
% 2.18/1.03  ac_symbols:                             0
% 2.18/1.03  
% 2.18/1.03  ------ Propositional Solver
% 2.18/1.03  
% 2.18/1.03  prop_solver_calls:                      27
% 2.18/1.03  prop_fast_solver_calls:                 896
% 2.18/1.03  smt_solver_calls:                       0
% 2.18/1.03  smt_fast_solver_calls:                  0
% 2.18/1.03  prop_num_of_clauses:                    711
% 2.18/1.03  prop_preprocess_simplified:             3510
% 2.18/1.03  prop_fo_subsumed:                       23
% 2.18/1.03  prop_solver_time:                       0.
% 2.18/1.03  smt_solver_time:                        0.
% 2.18/1.03  smt_fast_solver_time:                   0.
% 2.18/1.03  prop_fast_solver_time:                  0.
% 2.18/1.03  prop_unsat_core_time:                   0.
% 2.18/1.03  
% 2.18/1.03  ------ QBF
% 2.18/1.03  
% 2.18/1.03  qbf_q_res:                              0
% 2.18/1.03  qbf_num_tautologies:                    0
% 2.18/1.03  qbf_prep_cycles:                        0
% 2.18/1.03  
% 2.18/1.03  ------ BMC1
% 2.18/1.03  
% 2.18/1.03  bmc1_current_bound:                     -1
% 2.18/1.03  bmc1_last_solved_bound:                 -1
% 2.18/1.03  bmc1_unsat_core_size:                   -1
% 2.18/1.03  bmc1_unsat_core_parents_size:           -1
% 2.18/1.03  bmc1_merge_next_fun:                    0
% 2.18/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.03  
% 2.18/1.03  ------ Instantiation
% 2.18/1.03  
% 2.18/1.03  inst_num_of_clauses:                    193
% 2.18/1.03  inst_num_in_passive:                    2
% 2.18/1.03  inst_num_in_active:                     157
% 2.18/1.03  inst_num_in_unprocessed:                34
% 2.18/1.03  inst_num_of_loops:                      180
% 2.18/1.03  inst_num_of_learning_restarts:          0
% 2.18/1.03  inst_num_moves_active_passive:          18
% 2.18/1.03  inst_lit_activity:                      0
% 2.18/1.03  inst_lit_activity_moves:                0
% 2.18/1.03  inst_num_tautologies:                   0
% 2.18/1.03  inst_num_prop_implied:                  0
% 2.18/1.03  inst_num_existing_simplified:           0
% 2.18/1.03  inst_num_eq_res_simplified:             0
% 2.18/1.03  inst_num_child_elim:                    0
% 2.18/1.03  inst_num_of_dismatching_blockings:      41
% 2.18/1.03  inst_num_of_non_proper_insts:           199
% 2.18/1.03  inst_num_of_duplicates:                 0
% 2.18/1.03  inst_inst_num_from_inst_to_res:         0
% 2.18/1.03  inst_dismatching_checking_time:         0.
% 2.18/1.03  
% 2.18/1.03  ------ Resolution
% 2.18/1.03  
% 2.18/1.03  res_num_of_clauses:                     0
% 2.18/1.03  res_num_in_passive:                     0
% 2.18/1.03  res_num_in_active:                      0
% 2.18/1.03  res_num_of_loops:                       123
% 2.18/1.03  res_forward_subset_subsumed:            42
% 2.18/1.03  res_backward_subset_subsumed:           2
% 2.18/1.03  res_forward_subsumed:                   0
% 2.18/1.03  res_backward_subsumed:                  0
% 2.18/1.03  res_forward_subsumption_resolution:     0
% 2.18/1.03  res_backward_subsumption_resolution:    0
% 2.18/1.03  res_clause_to_clause_subsumption:       120
% 2.18/1.03  res_orphan_elimination:                 0
% 2.18/1.03  res_tautology_del:                      38
% 2.18/1.03  res_num_eq_res_simplified:              2
% 2.18/1.03  res_num_sel_changes:                    0
% 2.18/1.03  res_moves_from_active_to_pass:          0
% 2.18/1.03  
% 2.18/1.03  ------ Superposition
% 2.18/1.03  
% 2.18/1.03  sup_time_total:                         0.
% 2.18/1.03  sup_time_generating:                    0.
% 2.18/1.03  sup_time_sim_full:                      0.
% 2.18/1.03  sup_time_sim_immed:                     0.
% 2.18/1.03  
% 2.18/1.03  sup_num_of_clauses:                     41
% 2.18/1.03  sup_num_in_active:                      26
% 2.18/1.03  sup_num_in_passive:                     15
% 2.18/1.03  sup_num_of_loops:                       34
% 2.18/1.03  sup_fw_superposition:                   23
% 2.18/1.03  sup_bw_superposition:                   0
% 2.18/1.03  sup_immediate_simplified:               4
% 2.18/1.03  sup_given_eliminated:                   0
% 2.18/1.03  comparisons_done:                       0
% 2.18/1.03  comparisons_avoided:                    0
% 2.18/1.03  
% 2.18/1.03  ------ Simplifications
% 2.18/1.03  
% 2.18/1.03  
% 2.18/1.03  sim_fw_subset_subsumed:                 3
% 2.18/1.03  sim_bw_subset_subsumed:                 0
% 2.18/1.03  sim_fw_subsumed:                        0
% 2.18/1.03  sim_bw_subsumed:                        0
% 2.18/1.03  sim_fw_subsumption_res:                 0
% 2.18/1.03  sim_bw_subsumption_res:                 0
% 2.18/1.03  sim_tautology_del:                      0
% 2.18/1.03  sim_eq_tautology_del:                   0
% 2.18/1.03  sim_eq_res_simp:                        0
% 2.18/1.03  sim_fw_demodulated:                     0
% 2.18/1.03  sim_bw_demodulated:                     8
% 2.18/1.03  sim_light_normalised:                   1
% 2.18/1.03  sim_joinable_taut:                      0
% 2.18/1.03  sim_joinable_simp:                      0
% 2.18/1.03  sim_ac_normalised:                      0
% 2.18/1.03  sim_smt_subsumption:                    0
% 2.18/1.03  
%------------------------------------------------------------------------------
