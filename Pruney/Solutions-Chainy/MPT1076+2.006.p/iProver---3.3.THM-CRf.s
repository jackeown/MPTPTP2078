%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:21 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 945 expanded)
%              Number of clauses        :  100 ( 235 expanded)
%              Number of leaves         :   18 ( 356 expanded)
%              Depth                    :   20
%              Number of atoms          :  666 (7658 expanded)
%              Number of equality atoms :  162 (1061 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f42,f41,f40,f39,f38])).

fof(f67,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_751,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1211,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_748,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | m1_subset_1(k1_funct_1(X2,X5),X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | X5 != X0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_259])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(k1_funct_1(X1,X0),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(k1_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0_50,k1_relat_1(X1_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k1_funct_1(X1_50,X0_50),X1_51)
    | ~ v1_funct_1(X1_50)
    | ~ v1_relat_1(X1_50)
    | v1_xboole_0(k1_relat_1(X1_50)) ),
    inference(subtyping,[status(esa)],[c_286])).

cnf(c_1218,plain,
    ( m1_subset_1(X0_50,k1_relat_1(X1_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k1_funct_1(X1_50,X0_50),X1_51) = iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_xboole_0(k1_relat_1(X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_2382,plain,
    ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1218])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_503,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_504,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_506,plain,
    ( v1_partfun1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_25,c_23,c_21])).

cnf(c_737,plain,
    ( v1_partfun1(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_506])).

cnf(c_1225,plain,
    ( v1_partfun1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_754,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ v4_relat_1(X0_50,X0_51)
    | ~ v1_relat_1(X0_50)
    | k1_relat_1(X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1209,plain,
    ( k1_relat_1(X0_50) = X0_51
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | v4_relat_1(X0_50,X0_51) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_1926,plain,
    ( k1_relat_1(sK3) = sK1
    | v4_relat_1(sK3,sK1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1209])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_757,plain,
    ( v4_relat_1(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1438,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1416,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1574,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_758,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1595,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1911,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1996,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_25,c_23,c_21,c_504,c_1438,c_1574,c_1595,c_1911])).

cnf(c_2388,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2382,c_1996])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1575,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_1596,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1595])).

cnf(c_2412,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2388,c_27,c_28,c_30,c_1575,c_1596])).

cnf(c_2413,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2412])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_750,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1212,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_6,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_390,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_408,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_390,c_8])).

cnf(c_742,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ m1_subset_1(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_xboole_0(X0_51)
    | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_1220,plain,
    ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50)
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | m1_subset_1(X1_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2606,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1220])).

cnf(c_26,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2686,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
    | m1_subset_1(X0_50,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_26,c_31,c_34])).

cnf(c_2694,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_2686])).

cnf(c_2868,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1211,c_2694])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_416,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X0,X2) = k1_funct_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_6,c_13])).

cnf(c_741,plain,
    ( ~ v1_partfun1(X0_50,X0_51)
    | ~ m1_subset_1(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_xboole_0(X0_51)
    | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1221,plain,
    ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50)
    | v1_partfun1(X0_50,X0_51) != iProver_top
    | m1_subset_1(X1_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2497,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1221])).

cnf(c_2587,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
    | m1_subset_1(X0_50,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2497,c_26,c_31,c_34])).

cnf(c_2595,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_2587])).

cnf(c_2788,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1211,c_2595])).

cnf(c_2869,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2868,c_2788])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_440,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_441,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_445,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_25,c_24,c_23,c_21])).

cnf(c_446,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(renaming,[status(thm)],[c_445])).

cnf(c_740,plain,
    ( ~ v1_partfun1(X0_50,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ m1_subset_1(X1_50,sK1)
    | ~ v1_funct_1(X0_50)
    | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50)) ),
    inference(subtyping,[status(esa)],[c_446])).

cnf(c_1222,plain,
    ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50))
    | v1_partfun1(X0_50,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_2082,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_50,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1222])).

cnf(c_2245,plain,
    ( m1_subset_1(X0_50,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_31,c_34])).

cnf(c_2246,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2245])).

cnf(c_2253,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1211,c_2246])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_24,c_23,c_21])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_1224,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
    | m1_subset_1(X0_50,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_1816,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1211,c_1224])).

cnf(c_2254,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2253,c_1816])).

cnf(c_16,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_753,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1818,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1816,c_753])).

cnf(c_2309,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2254,c_1818])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2869,c_2309])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:39:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.36/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.99  
% 2.36/0.99  ------  iProver source info
% 2.36/0.99  
% 2.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.99  git: non_committed_changes: false
% 2.36/0.99  git: last_make_outside_of_git: false
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/0.99  --bmc1_symbol_reachability              true
% 2.36/0.99  --bmc1_property_lemmas                  false
% 2.36/0.99  --bmc1_k_induction                      false
% 2.36/0.99  --bmc1_non_equiv_states                 false
% 2.36/0.99  --bmc1_deadlock                         false
% 2.36/0.99  --bmc1_ucm                              false
% 2.36/0.99  --bmc1_add_unsat_core                   none
% 2.36/0.99  --bmc1_unsat_core_children              false
% 2.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.99  --bmc1_out_stat                         full
% 2.36/0.99  --bmc1_ground_init                      false
% 2.36/0.99  --bmc1_pre_inst_next_state              false
% 2.36/0.99  --bmc1_pre_inst_state                   false
% 2.36/0.99  --bmc1_pre_inst_reach_state             false
% 2.36/0.99  --bmc1_out_unsat_core                   false
% 2.36/0.99  --bmc1_aig_witness_out                  false
% 2.36/0.99  --bmc1_verbose                          false
% 2.36/0.99  --bmc1_dump_clauses_tptp                false
% 2.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.99  --bmc1_dump_file                        -
% 2.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.99  --bmc1_ucm_extend_mode                  1
% 2.36/0.99  --bmc1_ucm_init_mode                    2
% 2.36/0.99  --bmc1_ucm_cone_mode                    none
% 2.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.99  --bmc1_ucm_relax_model                  4
% 2.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.99  --bmc1_ucm_layered_model                none
% 2.36/0.99  --bmc1_ucm_max_lemma_size               10
% 2.36/0.99  
% 2.36/0.99  ------ AIG Options
% 2.36/0.99  
% 2.36/0.99  --aig_mode                              false
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation Options
% 2.36/0.99  
% 2.36/0.99  --instantiation_flag                    true
% 2.36/0.99  --inst_sos_flag                         false
% 2.36/0.99  --inst_sos_phase                        true
% 2.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel_side                     num_symb
% 2.36/0.99  --inst_solver_per_active                1400
% 2.36/0.99  --inst_solver_calls_frac                1.
% 2.36/0.99  --inst_passive_queue_type               priority_queues
% 2.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.99  --inst_passive_queues_freq              [25;2]
% 2.36/0.99  --inst_dismatching                      true
% 2.36/0.99  --inst_eager_unprocessed_to_passive     true
% 2.36/0.99  --inst_prop_sim_given                   true
% 2.36/0.99  --inst_prop_sim_new                     false
% 2.36/0.99  --inst_subs_new                         false
% 2.36/0.99  --inst_eq_res_simp                      false
% 2.36/0.99  --inst_subs_given                       false
% 2.36/0.99  --inst_orphan_elimination               true
% 2.36/0.99  --inst_learning_loop_flag               true
% 2.36/0.99  --inst_learning_start                   3000
% 2.36/0.99  --inst_learning_factor                  2
% 2.36/0.99  --inst_start_prop_sim_after_learn       3
% 2.36/0.99  --inst_sel_renew                        solver
% 2.36/0.99  --inst_lit_activity_flag                true
% 2.36/0.99  --inst_restr_to_given                   false
% 2.36/0.99  --inst_activity_threshold               500
% 2.36/0.99  --inst_out_proof                        true
% 2.36/0.99  
% 2.36/0.99  ------ Resolution Options
% 2.36/0.99  
% 2.36/0.99  --resolution_flag                       true
% 2.36/0.99  --res_lit_sel                           adaptive
% 2.36/0.99  --res_lit_sel_side                      none
% 2.36/0.99  --res_ordering                          kbo
% 2.36/0.99  --res_to_prop_solver                    active
% 2.36/0.99  --res_prop_simpl_new                    false
% 2.36/0.99  --res_prop_simpl_given                  true
% 2.36/0.99  --res_passive_queue_type                priority_queues
% 2.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.99  --res_passive_queues_freq               [15;5]
% 2.36/0.99  --res_forward_subs                      full
% 2.36/0.99  --res_backward_subs                     full
% 2.36/0.99  --res_forward_subs_resolution           true
% 2.36/0.99  --res_backward_subs_resolution          true
% 2.36/0.99  --res_orphan_elimination                true
% 2.36/0.99  --res_time_limit                        2.
% 2.36/0.99  --res_out_proof                         true
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Options
% 2.36/0.99  
% 2.36/0.99  --superposition_flag                    true
% 2.36/0.99  --sup_passive_queue_type                priority_queues
% 2.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.99  --demod_completeness_check              fast
% 2.36/0.99  --demod_use_ground                      true
% 2.36/0.99  --sup_to_prop_solver                    passive
% 2.36/0.99  --sup_prop_simpl_new                    true
% 2.36/0.99  --sup_prop_simpl_given                  true
% 2.36/0.99  --sup_fun_splitting                     false
% 2.36/0.99  --sup_smt_interval                      50000
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Simplification Setup
% 2.36/0.99  
% 2.36/0.99  --sup_indices_passive                   []
% 2.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_full_bw                           [BwDemod]
% 2.36/0.99  --sup_immed_triv                        [TrivRules]
% 2.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_immed_bw_main                     []
% 2.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  
% 2.36/0.99  ------ Combination Options
% 2.36/0.99  
% 2.36/0.99  --comb_res_mult                         3
% 2.36/0.99  --comb_sup_mult                         2
% 2.36/0.99  --comb_inst_mult                        10
% 2.36/0.99  
% 2.36/0.99  ------ Debug Options
% 2.36/0.99  
% 2.36/0.99  --dbg_backtrace                         false
% 2.36/0.99  --dbg_dump_prop_clauses                 false
% 2.36/0.99  --dbg_dump_prop_clauses_file            -
% 2.36/0.99  --dbg_out_stat                          false
% 2.36/0.99  ------ Parsing...
% 2.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.99  ------ Proving...
% 2.36/0.99  ------ Problem Properties 
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  clauses                                 23
% 2.36/0.99  conjectures                             9
% 2.36/0.99  EPR                                     7
% 2.36/0.99  Horn                                    19
% 2.36/0.99  unary                                   11
% 2.36/0.99  binary                                  3
% 2.36/0.99  lits                                    63
% 2.36/0.99  lits eq                                 8
% 2.36/0.99  fd_pure                                 0
% 2.36/0.99  fd_pseudo                               0
% 2.36/0.99  fd_cond                                 0
% 2.36/0.99  fd_pseudo_cond                          1
% 2.36/0.99  AC symbols                              0
% 2.36/0.99  
% 2.36/0.99  ------ Schedule dynamic 5 is on 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  Current options:
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/0.99  --bmc1_symbol_reachability              true
% 2.36/0.99  --bmc1_property_lemmas                  false
% 2.36/0.99  --bmc1_k_induction                      false
% 2.36/0.99  --bmc1_non_equiv_states                 false
% 2.36/0.99  --bmc1_deadlock                         false
% 2.36/0.99  --bmc1_ucm                              false
% 2.36/0.99  --bmc1_add_unsat_core                   none
% 2.36/0.99  --bmc1_unsat_core_children              false
% 2.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.99  --bmc1_out_stat                         full
% 2.36/0.99  --bmc1_ground_init                      false
% 2.36/0.99  --bmc1_pre_inst_next_state              false
% 2.36/0.99  --bmc1_pre_inst_state                   false
% 2.36/0.99  --bmc1_pre_inst_reach_state             false
% 2.36/0.99  --bmc1_out_unsat_core                   false
% 2.36/0.99  --bmc1_aig_witness_out                  false
% 2.36/0.99  --bmc1_verbose                          false
% 2.36/0.99  --bmc1_dump_clauses_tptp                false
% 2.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.99  --bmc1_dump_file                        -
% 2.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.99  --bmc1_ucm_extend_mode                  1
% 2.36/0.99  --bmc1_ucm_init_mode                    2
% 2.36/0.99  --bmc1_ucm_cone_mode                    none
% 2.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.99  --bmc1_ucm_relax_model                  4
% 2.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.99  --bmc1_ucm_layered_model                none
% 2.36/0.99  --bmc1_ucm_max_lemma_size               10
% 2.36/0.99  
% 2.36/0.99  ------ AIG Options
% 2.36/0.99  
% 2.36/0.99  --aig_mode                              false
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation Options
% 2.36/0.99  
% 2.36/0.99  --instantiation_flag                    true
% 2.36/0.99  --inst_sos_flag                         false
% 2.36/0.99  --inst_sos_phase                        true
% 2.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel_side                     none
% 2.36/0.99  --inst_solver_per_active                1400
% 2.36/0.99  --inst_solver_calls_frac                1.
% 2.36/0.99  --inst_passive_queue_type               priority_queues
% 2.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.99  --inst_passive_queues_freq              [25;2]
% 2.36/0.99  --inst_dismatching                      true
% 2.36/0.99  --inst_eager_unprocessed_to_passive     true
% 2.36/0.99  --inst_prop_sim_given                   true
% 2.36/0.99  --inst_prop_sim_new                     false
% 2.36/0.99  --inst_subs_new                         false
% 2.36/0.99  --inst_eq_res_simp                      false
% 2.36/0.99  --inst_subs_given                       false
% 2.36/0.99  --inst_orphan_elimination               true
% 2.36/0.99  --inst_learning_loop_flag               true
% 2.36/0.99  --inst_learning_start                   3000
% 2.36/0.99  --inst_learning_factor                  2
% 2.36/0.99  --inst_start_prop_sim_after_learn       3
% 2.36/0.99  --inst_sel_renew                        solver
% 2.36/0.99  --inst_lit_activity_flag                true
% 2.36/0.99  --inst_restr_to_given                   false
% 2.36/0.99  --inst_activity_threshold               500
% 2.36/0.99  --inst_out_proof                        true
% 2.36/0.99  
% 2.36/0.99  ------ Resolution Options
% 2.36/0.99  
% 2.36/0.99  --resolution_flag                       false
% 2.36/0.99  --res_lit_sel                           adaptive
% 2.36/0.99  --res_lit_sel_side                      none
% 2.36/0.99  --res_ordering                          kbo
% 2.36/0.99  --res_to_prop_solver                    active
% 2.36/0.99  --res_prop_simpl_new                    false
% 2.36/0.99  --res_prop_simpl_given                  true
% 2.36/0.99  --res_passive_queue_type                priority_queues
% 2.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.99  --res_passive_queues_freq               [15;5]
% 2.36/0.99  --res_forward_subs                      full
% 2.36/0.99  --res_backward_subs                     full
% 2.36/0.99  --res_forward_subs_resolution           true
% 2.36/0.99  --res_backward_subs_resolution          true
% 2.36/0.99  --res_orphan_elimination                true
% 2.36/0.99  --res_time_limit                        2.
% 2.36/0.99  --res_out_proof                         true
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Options
% 2.36/0.99  
% 2.36/0.99  --superposition_flag                    true
% 2.36/0.99  --sup_passive_queue_type                priority_queues
% 2.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.99  --demod_completeness_check              fast
% 2.36/0.99  --demod_use_ground                      true
% 2.36/0.99  --sup_to_prop_solver                    passive
% 2.36/0.99  --sup_prop_simpl_new                    true
% 2.36/0.99  --sup_prop_simpl_given                  true
% 2.36/0.99  --sup_fun_splitting                     false
% 2.36/0.99  --sup_smt_interval                      50000
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Simplification Setup
% 2.36/0.99  
% 2.36/0.99  --sup_indices_passive                   []
% 2.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_full_bw                           [BwDemod]
% 2.36/0.99  --sup_immed_triv                        [TrivRules]
% 2.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_immed_bw_main                     []
% 2.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  
% 2.36/0.99  ------ Combination Options
% 2.36/0.99  
% 2.36/0.99  --comb_res_mult                         3
% 2.36/0.99  --comb_sup_mult                         2
% 2.36/0.99  --comb_inst_mult                        10
% 2.36/0.99  
% 2.36/0.99  ------ Debug Options
% 2.36/0.99  
% 2.36/0.99  --dbg_backtrace                         false
% 2.36/0.99  --dbg_dump_prop_clauses                 false
% 2.36/0.99  --dbg_dump_prop_clauses_file            -
% 2.36/0.99  --dbg_out_stat                          false
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  ------ Proving...
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  % SZS status Theorem for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  fof(f13,conjecture,(
% 2.36/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f14,negated_conjecture,(
% 2.36/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.36/0.99    inference(negated_conjecture,[],[f13])).
% 2.36/0.99  
% 2.36/0.99  fof(f35,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f14])).
% 2.36/0.99  
% 2.36/0.99  fof(f36,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f35])).
% 2.36/0.99  
% 2.36/0.99  fof(f42,plain,(
% 2.36/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f41,plain,(
% 2.36/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f40,plain,(
% 2.36/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f39,plain,(
% 2.36/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f38,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f43,plain,(
% 2.36/0.99    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f42,f41,f40,f39,f38])).
% 2.36/0.99  
% 2.36/0.99  fof(f67,plain,(
% 2.36/0.99    m1_subset_1(sK5,sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f64,plain,(
% 2.36/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f1,axiom,(
% 2.36/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f15,plain,(
% 2.36/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.36/0.99    inference(ennf_transformation,[],[f1])).
% 2.36/0.99  
% 2.36/0.99  fof(f16,plain,(
% 2.36/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.36/0.99    inference(flattening,[],[f15])).
% 2.36/0.99  
% 2.36/0.99  fof(f44,plain,(
% 2.36/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f16])).
% 2.36/0.99  
% 2.36/0.99  fof(f5,axiom,(
% 2.36/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f20,plain,(
% 2.36/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.99    inference(ennf_transformation,[],[f5])).
% 2.36/0.99  
% 2.36/0.99  fof(f49,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.99    inference(cnf_transformation,[],[f20])).
% 2.36/0.99  
% 2.36/0.99  fof(f4,axiom,(
% 2.36/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f18,plain,(
% 2.36/0.99    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.36/0.99    inference(ennf_transformation,[],[f4])).
% 2.36/0.99  
% 2.36/0.99  fof(f19,plain,(
% 2.36/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.36/0.99    inference(flattening,[],[f18])).
% 2.36/0.99  
% 2.36/0.99  fof(f47,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f19])).
% 2.36/0.99  
% 2.36/0.99  fof(f8,axiom,(
% 2.36/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f25,plain,(
% 2.36/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.36/0.99    inference(ennf_transformation,[],[f8])).
% 2.36/0.99  
% 2.36/0.99  fof(f26,plain,(
% 2.36/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.36/0.99    inference(flattening,[],[f25])).
% 2.36/0.99  
% 2.36/0.99  fof(f54,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f26])).
% 2.36/0.99  
% 2.36/0.99  fof(f63,plain,(
% 2.36/0.99    v1_funct_2(sK3,sK1,sK0)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f60,plain,(
% 2.36/0.99    ~v1_xboole_0(sK0)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f62,plain,(
% 2.36/0.99    v1_funct_1(sK3)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f9,axiom,(
% 2.36/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f27,plain,(
% 2.36/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.36/0.99    inference(ennf_transformation,[],[f9])).
% 2.36/0.99  
% 2.36/0.99  fof(f28,plain,(
% 2.36/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/0.99    inference(flattening,[],[f27])).
% 2.36/0.99  
% 2.36/0.99  fof(f37,plain,(
% 2.36/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/0.99    inference(nnf_transformation,[],[f28])).
% 2.36/0.99  
% 2.36/0.99  fof(f55,plain,(
% 2.36/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f37])).
% 2.36/0.99  
% 2.36/0.99  fof(f48,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.99    inference(cnf_transformation,[],[f20])).
% 2.36/0.99  
% 2.36/0.99  fof(f2,axiom,(
% 2.36/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f17,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f2])).
% 2.36/0.99  
% 2.36/0.99  fof(f45,plain,(
% 2.36/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f17])).
% 2.36/0.99  
% 2.36/0.99  fof(f3,axiom,(
% 2.36/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f46,plain,(
% 2.36/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.36/0.99    inference(cnf_transformation,[],[f3])).
% 2.36/0.99  
% 2.36/0.99  fof(f61,plain,(
% 2.36/0.99    ~v1_xboole_0(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f66,plain,(
% 2.36/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f6,axiom,(
% 2.36/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f21,plain,(
% 2.36/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.99    inference(ennf_transformation,[],[f6])).
% 2.36/0.99  
% 2.36/0.99  fof(f22,plain,(
% 2.36/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/0.99    inference(flattening,[],[f21])).
% 2.36/0.99  
% 2.36/0.99  fof(f51,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/0.99    inference(cnf_transformation,[],[f22])).
% 2.36/0.99  
% 2.36/0.99  fof(f11,axiom,(
% 2.36/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f31,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f11])).
% 2.36/0.99  
% 2.36/0.99  fof(f32,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f31])).
% 2.36/0.99  
% 2.36/0.99  fof(f58,plain,(
% 2.36/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f32])).
% 2.36/0.99  
% 2.36/0.99  fof(f7,axiom,(
% 2.36/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f23,plain,(
% 2.36/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f7])).
% 2.36/0.99  
% 2.36/0.99  fof(f24,plain,(
% 2.36/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f23])).
% 2.36/0.99  
% 2.36/0.99  fof(f52,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f24])).
% 2.36/0.99  
% 2.36/0.99  fof(f65,plain,(
% 2.36/0.99    v1_funct_1(sK4)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f68,plain,(
% 2.36/0.99    v1_partfun1(sK4,sK0)),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f10,axiom,(
% 2.36/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f29,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f10])).
% 2.36/0.99  
% 2.36/0.99  fof(f30,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f29])).
% 2.36/0.99  
% 2.36/0.99  fof(f57,plain,(
% 2.36/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f30])).
% 2.36/0.99  
% 2.36/0.99  fof(f12,axiom,(
% 2.36/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5)))))))),
% 2.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f33,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f12])).
% 2.36/0.99  
% 2.36/0.99  fof(f34,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f33])).
% 2.36/0.99  
% 2.36/0.99  fof(f59,plain,(
% 2.36/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) = k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f34])).
% 2.36/0.99  
% 2.36/0.99  fof(f69,plain,(
% 2.36/0.99    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.36/0.99    inference(cnf_transformation,[],[f43])).
% 2.36/0.99  
% 2.36/0.99  cnf(c_18,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK5,sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_751,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK5,sK1) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1211,plain,
% 2.36/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_21,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.36/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_748,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1214,plain,
% 2.36/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_0,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_4,plain,
% 2.36/0.99      ( v5_relat_1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.36/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3,plain,
% 2.36/0.99      ( ~ v5_relat_1(X0,X1)
% 2.36/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.36/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | ~ v1_relat_1(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_259,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.36/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | ~ v1_relat_1(X0) ),
% 2.36/0.99      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_285,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.36/0.99      | m1_subset_1(k1_funct_1(X2,X5),X4)
% 2.36/0.99      | ~ v1_funct_1(X2)
% 2.36/0.99      | ~ v1_relat_1(X2)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | X5 != X0
% 2.36/0.99      | k1_relat_1(X2) != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_259]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_286,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.36/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.36/0.99      | m1_subset_1(k1_funct_1(X1,X0),X3)
% 2.36/0.99      | ~ v1_funct_1(X1)
% 2.36/0.99      | ~ v1_relat_1(X1)
% 2.36/0.99      | v1_xboole_0(k1_relat_1(X1)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_285]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_744,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_50,k1_relat_1(X1_50))
% 2.36/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.36/0.99      | m1_subset_1(k1_funct_1(X1_50,X0_50),X1_51)
% 2.36/0.99      | ~ v1_funct_1(X1_50)
% 2.36/0.99      | ~ v1_relat_1(X1_50)
% 2.36/0.99      | v1_xboole_0(k1_relat_1(X1_50)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_286]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1218,plain,
% 2.36/0.99      ( m1_subset_1(X0_50,k1_relat_1(X1_50)) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.36/0.99      | m1_subset_1(k1_funct_1(X1_50,X0_50),X1_51) = iProver_top
% 2.36/0.99      | v1_funct_1(X1_50) != iProver_top
% 2.36/0.99      | v1_relat_1(X1_50) != iProver_top
% 2.36/0.99      | v1_xboole_0(k1_relat_1(X1_50)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2382,plain,
% 2.36/0.99      ( m1_subset_1(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.36/0.99      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.36/0.99      | v1_funct_1(sK3) != iProver_top
% 2.36/0.99      | v1_relat_1(sK3) != iProver_top
% 2.36/0.99      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1214,c_1218]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_9,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X2) ),
% 2.36/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_22,negated_conjecture,
% 2.36/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_503,plain,
% 2.36/0.99      ( v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X2)
% 2.36/0.99      | sK3 != X0
% 2.36/0.99      | sK0 != X2
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_504,plain,
% 2.36/0.99      ( v1_partfun1(sK3,sK1)
% 2.36/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.36/0.99      | ~ v1_funct_1(sK3)
% 2.36/0.99      | v1_xboole_0(sK0) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_503]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_25,negated_conjecture,
% 2.36/0.99      ( ~ v1_xboole_0(sK0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_23,negated_conjecture,
% 2.36/0.99      ( v1_funct_1(sK3) ),
% 2.36/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_506,plain,
% 2.36/0.99      ( v1_partfun1(sK3,sK1) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_504,c_25,c_23,c_21]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_737,plain,
% 2.36/0.99      ( v1_partfun1(sK3,sK1) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_506]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1225,plain,
% 2.36/0.99      ( v1_partfun1(sK3,sK1) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_12,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ v4_relat_1(X0,X1)
% 2.36/0.99      | ~ v1_relat_1(X0)
% 2.36/0.99      | k1_relat_1(X0) = X1 ),
% 2.36/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_754,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0_50,X0_51)
% 2.36/0.99      | ~ v4_relat_1(X0_50,X0_51)
% 2.36/0.99      | ~ v1_relat_1(X0_50)
% 2.36/0.99      | k1_relat_1(X0_50) = X0_51 ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1209,plain,
% 2.36/0.99      ( k1_relat_1(X0_50) = X0_51
% 2.36/0.99      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.36/0.99      | v4_relat_1(X0_50,X0_51) != iProver_top
% 2.36/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1926,plain,
% 2.36/0.99      ( k1_relat_1(sK3) = sK1
% 2.36/0.99      | v4_relat_1(sK3,sK1) != iProver_top
% 2.36/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1225,c_1209]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_5,plain,
% 2.36/0.99      ( v4_relat_1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.36/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_757,plain,
% 2.36/0.99      ( v4_relat_1(X0_50,X0_51)
% 2.36/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1438,plain,
% 2.36/0.99      ( v4_relat_1(sK3,sK1)
% 2.36/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_757]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/0.99      | ~ v1_relat_1(X1)
% 2.36/0.99      | v1_relat_1(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_759,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.36/0.99      | ~ v1_relat_1(X1_50)
% 2.36/0.99      | v1_relat_1(X0_50) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1416,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.36/0.99      | v1_relat_1(X0_50)
% 2.36/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_759]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1574,plain,
% 2.36/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.36/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.36/0.99      | v1_relat_1(sK3) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2,plain,
% 2.36/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_758,plain,
% 2.36/0.99      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1595,plain,
% 2.36/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1911,plain,
% 2.36/0.99      ( ~ v1_partfun1(sK3,sK1)
% 2.36/0.99      | ~ v4_relat_1(sK3,sK1)
% 2.36/0.99      | ~ v1_relat_1(sK3)
% 2.36/0.99      | k1_relat_1(sK3) = sK1 ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_754]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1996,plain,
% 2.36/0.99      ( k1_relat_1(sK3) = sK1 ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1926,c_25,c_23,c_21,c_504,c_1438,c_1574,c_1595,c_1911]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2388,plain,
% 2.36/0.99      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.36/0.99      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.36/0.99      | v1_funct_1(sK3) != iProver_top
% 2.36/0.99      | v1_relat_1(sK3) != iProver_top
% 2.36/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_2382,c_1996]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_24,negated_conjecture,
% 2.36/0.99      ( ~ v1_xboole_0(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_27,plain,
% 2.36/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_28,plain,
% 2.36/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_30,plain,
% 2.36/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1575,plain,
% 2.36/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.36/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.36/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1596,plain,
% 2.36/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1595]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2412,plain,
% 2.36/0.99      ( m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_2388,c_27,c_28,c_30,c_1575,c_1596]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2413,plain,
% 2.36/0.99      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.36/0.99      | m1_subset_1(k1_funct_1(sK3,X0_50),sK0) = iProver_top ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_2412]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_19,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.36/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_750,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1212,plain,
% 2.36/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_6,plain,
% 2.36/0.99      ( v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_14,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X2)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 2.36/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_390,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | v1_xboole_0(X3)
% 2.36/0.99      | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
% 2.36/0.99      inference(resolution,[status(thm)],[c_6,c_14]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_8,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_xboole_0(X2)
% 2.36/0.99      | v1_xboole_0(X1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_408,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X1,X3,X0,X2) = k7_partfun1(X3,X0,X2) ),
% 2.36/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_390,c_8]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_742,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0_50,X0_51)
% 2.36/0.99      | ~ m1_subset_1(X1_50,X0_51)
% 2.36/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.36/0.99      | ~ v1_funct_1(X0_50)
% 2.36/0.99      | v1_xboole_0(X0_51)
% 2.36/0.99      | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_408]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1220,plain,
% 2.36/0.99      ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k7_partfun1(X1_51,X0_50,X1_50)
% 2.36/0.99      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_50,X0_51) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.36/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.36/0.99      | v1_xboole_0(X0_51) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2606,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
% 2.36/0.99      | v1_partfun1(sK4,sK0) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,sK0) != iProver_top
% 2.36/0.99      | v1_funct_1(sK4) != iProver_top
% 2.36/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1212,c_1220]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_26,plain,
% 2.36/0.99      ( v1_xboole_0(sK0) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_20,negated_conjecture,
% 2.36/0.99      ( v1_funct_1(sK4) ),
% 2.36/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_31,plain,
% 2.36/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_17,negated_conjecture,
% 2.36/0.99      ( v1_partfun1(sK4,sK0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_34,plain,
% 2.36/0.99      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2686,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k7_partfun1(sK2,sK4,X0_50)
% 2.36/0.99      | m1_subset_1(X0_50,sK0) != iProver_top ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_2606,c_26,c_31,c_34]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2694,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0_50))
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_2413,c_2686]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2868,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1211,c_2694]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_13,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.36/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_416,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X1,X3,X0,X2) = k1_funct_1(X0,X2) ),
% 2.36/0.99      inference(resolution,[status(thm)],[c_6,c_13]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_741,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0_50,X0_51)
% 2.36/0.99      | ~ m1_subset_1(X1_50,X0_51)
% 2.36/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.36/0.99      | ~ v1_funct_1(X0_50)
% 2.36/0.99      | v1_xboole_0(X0_51)
% 2.36/0.99      | k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_416]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1221,plain,
% 2.36/0.99      ( k3_funct_2(X0_51,X1_51,X0_50,X1_50) = k1_funct_1(X0_50,X1_50)
% 2.36/0.99      | v1_partfun1(X0_50,X0_51) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_50,X0_51) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.36/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.36/0.99      | v1_xboole_0(X0_51) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2497,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.36/0.99      | v1_partfun1(sK4,sK0) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,sK0) != iProver_top
% 2.36/0.99      | v1_funct_1(sK4) != iProver_top
% 2.36/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1212,c_1221]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2587,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,X0_50) = k1_funct_1(sK4,X0_50)
% 2.36/0.99      | m1_subset_1(X0_50,sK0) != iProver_top ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_2497,c_26,c_31,c_34]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2595,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0_50)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_50))
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_2413,c_2587]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2788,plain,
% 2.36/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1211,c_2595]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2869,plain,
% 2.36/0.99      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_2868,c_2788]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_15,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ v1_partfun1(X3,X2)
% 2.36/0.99      | ~ m1_subset_1(X4,X1)
% 2.36/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X3)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | v1_xboole_0(X2)
% 2.36/0.99      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_440,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,X3)
% 2.36/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 2.36/0.99      | ~ v1_funct_1(X4)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | v1_xboole_0(X3)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
% 2.36/0.99      | sK3 != X4
% 2.36/0.99      | sK0 != X1
% 2.36/0.99      | sK1 != X3 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_441,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,sK0)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.36/0.99      | ~ m1_subset_1(X2,sK1)
% 2.36/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | ~ v1_funct_1(sK3)
% 2.36/0.99      | v1_xboole_0(sK0)
% 2.36/0.99      | v1_xboole_0(sK1)
% 2.36/0.99      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_445,plain,
% 2.36/0.99      ( ~ v1_funct_1(X0)
% 2.36/0.99      | ~ v1_partfun1(X0,sK0)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.36/0.99      | ~ m1_subset_1(X2,sK1)
% 2.36/0.99      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_441,c_25,c_24,c_23,c_21]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_446,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0,sK0)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.36/0.99      | ~ m1_subset_1(X2,sK1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_445]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_740,plain,
% 2.36/0.99      ( ~ v1_partfun1(X0_50,sK0)
% 2.36/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 2.36/0.99      | ~ m1_subset_1(X1_50,sK1)
% 2.36/0.99      | ~ v1_funct_1(X0_50)
% 2.36/0.99      | k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_446]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1222,plain,
% 2.36/0.99      ( k3_funct_2(sK1,X0_51,k8_funct_2(sK1,sK0,X0_51,sK3,X0_50),X1_50) = k1_funct_1(X0_50,k3_funct_2(sK1,sK0,sK3,X1_50))
% 2.36/0.99      | v1_partfun1(X0_50,sK0) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_50,sK1) != iProver_top
% 2.36/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2082,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.36/0.99      | v1_partfun1(sK4,sK0) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top
% 2.36/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1212,c_1222]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2245,plain,
% 2.36/0.99      ( m1_subset_1(X0_50,sK1) != iProver_top
% 2.36/0.99      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_2082,c_31,c_34]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2246,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_50) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_50))
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_2245]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2253,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1211,c_2246]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_485,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.36/0.99      | ~ v1_funct_1(X2)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 2.36/0.99      | sK3 != X2
% 2.36/0.99      | sK0 != X3
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_486,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,sK1)
% 2.36/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.36/0.99      | ~ v1_funct_1(sK3)
% 2.36/0.99      | v1_xboole_0(sK1)
% 2.36/0.99      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_490,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,sK1)
% 2.36/0.99      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_486,c_24,c_23,c_21]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_738,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_50,sK1)
% 2.36/0.99      | k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_490]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1224,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK0,sK3,X0_50) = k1_funct_1(sK3,X0_50)
% 2.36/0.99      | m1_subset_1(X0_50,sK1) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1816,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1211,c_1224]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2254,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_2253,c_1816]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_16,negated_conjecture,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_753,negated_conjecture,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1818,plain,
% 2.36/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(demodulation,[status(thm)],[c_1816,c_753]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2309,plain,
% 2.36/0.99      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.36/0.99      inference(demodulation,[status(thm)],[c_2254,c_1818]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(contradiction,plain,
% 2.36/0.99      ( $false ),
% 2.36/0.99      inference(minisat,[status(thm)],[c_2869,c_2309]) ).
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  ------                               Statistics
% 2.36/0.99  
% 2.36/0.99  ------ General
% 2.36/0.99  
% 2.36/0.99  abstr_ref_over_cycles:                  0
% 2.36/0.99  abstr_ref_under_cycles:                 0
% 2.36/0.99  gc_basic_clause_elim:                   0
% 2.36/0.99  forced_gc_time:                         0
% 2.36/0.99  parsing_time:                           0.009
% 2.36/0.99  unif_index_cands_time:                  0.
% 2.36/0.99  unif_index_add_time:                    0.
% 2.36/0.99  orderings_time:                         0.
% 2.36/0.99  out_proof_time:                         0.01
% 2.36/0.99  total_time:                             0.135
% 2.36/0.99  num_of_symbols:                         55
% 2.36/0.99  num_of_terms:                           3175
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing
% 2.36/0.99  
% 2.36/0.99  num_of_splits:                          0
% 2.36/0.99  num_of_split_atoms:                     0
% 2.36/0.99  num_of_reused_defs:                     0
% 2.36/0.99  num_eq_ax_congr_red:                    10
% 2.36/0.99  num_of_sem_filtered_clauses:            1
% 2.36/0.99  num_of_subtypes:                        2
% 2.36/0.99  monotx_restored_types:                  0
% 2.36/0.99  sat_num_of_epr_types:                   0
% 2.36/0.99  sat_num_of_non_cyclic_types:            0
% 2.36/0.99  sat_guarded_non_collapsed_types:        1
% 2.36/0.99  num_pure_diseq_elim:                    0
% 2.36/0.99  simp_replaced_by:                       0
% 2.36/0.99  res_preprocessed:                       126
% 2.36/0.99  prep_upred:                             0
% 2.36/0.99  prep_unflattend:                        18
% 2.36/0.99  smt_new_axioms:                         0
% 2.36/0.99  pred_elim_cands:                        6
% 2.36/0.99  pred_elim:                              3
% 2.36/0.99  pred_elim_cl:                           1
% 2.36/0.99  pred_elim_cycles:                       6
% 2.36/0.99  merged_defs:                            0
% 2.36/0.99  merged_defs_ncl:                        0
% 2.36/0.99  bin_hyper_res:                          0
% 2.36/0.99  prep_cycles:                            4
% 2.36/0.99  pred_elim_time:                         0.007
% 2.36/0.99  splitting_time:                         0.
% 2.36/0.99  sem_filter_time:                        0.
% 2.36/0.99  monotx_time:                            0.
% 2.36/0.99  subtype_inf_time:                       0.
% 2.36/0.99  
% 2.36/0.99  ------ Problem properties
% 2.36/0.99  
% 2.36/0.99  clauses:                                23
% 2.36/0.99  conjectures:                            9
% 2.36/0.99  epr:                                    7
% 2.36/0.99  horn:                                   19
% 2.36/0.99  ground:                                 10
% 2.36/0.99  unary:                                  11
% 2.36/0.99  binary:                                 3
% 2.36/0.99  lits:                                   63
% 2.36/0.99  lits_eq:                                8
% 2.36/0.99  fd_pure:                                0
% 2.36/0.99  fd_pseudo:                              0
% 2.36/0.99  fd_cond:                                0
% 2.36/0.99  fd_pseudo_cond:                         1
% 2.36/0.99  ac_symbols:                             0
% 2.36/0.99  
% 2.36/0.99  ------ Propositional Solver
% 2.36/0.99  
% 2.36/0.99  prop_solver_calls:                      27
% 2.36/0.99  prop_fast_solver_calls:                 937
% 2.36/0.99  smt_solver_calls:                       0
% 2.36/0.99  smt_fast_solver_calls:                  0
% 2.36/0.99  prop_num_of_clauses:                    925
% 2.36/0.99  prop_preprocess_simplified:             4059
% 2.36/0.99  prop_fo_subsumed:                       36
% 2.36/0.99  prop_solver_time:                       0.
% 2.36/0.99  smt_solver_time:                        0.
% 2.36/0.99  smt_fast_solver_time:                   0.
% 2.36/0.99  prop_fast_solver_time:                  0.
% 2.36/0.99  prop_unsat_core_time:                   0.
% 2.36/0.99  
% 2.36/0.99  ------ QBF
% 2.36/0.99  
% 2.36/0.99  qbf_q_res:                              0
% 2.36/0.99  qbf_num_tautologies:                    0
% 2.36/0.99  qbf_prep_cycles:                        0
% 2.36/0.99  
% 2.36/0.99  ------ BMC1
% 2.36/0.99  
% 2.36/0.99  bmc1_current_bound:                     -1
% 2.36/0.99  bmc1_last_solved_bound:                 -1
% 2.36/0.99  bmc1_unsat_core_size:                   -1
% 2.36/0.99  bmc1_unsat_core_parents_size:           -1
% 2.36/0.99  bmc1_merge_next_fun:                    0
% 2.36/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation
% 2.36/0.99  
% 2.36/0.99  inst_num_of_clauses:                    303
% 2.36/0.99  inst_num_in_passive:                    38
% 2.36/0.99  inst_num_in_active:                     203
% 2.36/0.99  inst_num_in_unprocessed:                62
% 2.36/0.99  inst_num_of_loops:                      220
% 2.36/0.99  inst_num_of_learning_restarts:          0
% 2.36/0.99  inst_num_moves_active_passive:          12
% 2.36/0.99  inst_lit_activity:                      0
% 2.36/0.99  inst_lit_activity_moves:                0
% 2.36/0.99  inst_num_tautologies:                   0
% 2.36/0.99  inst_num_prop_implied:                  0
% 2.36/0.99  inst_num_existing_simplified:           0
% 2.36/0.99  inst_num_eq_res_simplified:             0
% 2.36/0.99  inst_num_child_elim:                    0
% 2.36/0.99  inst_num_of_dismatching_blockings:      54
% 2.36/0.99  inst_num_of_non_proper_insts:           276
% 2.36/0.99  inst_num_of_duplicates:                 0
% 2.36/0.99  inst_inst_num_from_inst_to_res:         0
% 2.36/0.99  inst_dismatching_checking_time:         0.
% 2.36/0.99  
% 2.36/0.99  ------ Resolution
% 2.36/0.99  
% 2.36/0.99  res_num_of_clauses:                     0
% 2.36/0.99  res_num_in_passive:                     0
% 2.36/0.99  res_num_in_active:                      0
% 2.36/0.99  res_num_of_loops:                       130
% 2.36/0.99  res_forward_subset_subsumed:            36
% 2.36/0.99  res_backward_subset_subsumed:           2
% 2.36/0.99  res_forward_subsumed:                   0
% 2.36/0.99  res_backward_subsumed:                  0
% 2.36/0.99  res_forward_subsumption_resolution:     2
% 2.36/0.99  res_backward_subsumption_resolution:    0
% 2.36/0.99  res_clause_to_clause_subsumption:       51
% 2.36/0.99  res_orphan_elimination:                 0
% 2.36/0.99  res_tautology_del:                      26
% 2.36/0.99  res_num_eq_res_simplified:              0
% 2.36/0.99  res_num_sel_changes:                    0
% 2.36/0.99  res_moves_from_active_to_pass:          0
% 2.36/0.99  
% 2.36/0.99  ------ Superposition
% 2.36/0.99  
% 2.36/0.99  sup_time_total:                         0.
% 2.36/0.99  sup_time_generating:                    0.
% 2.36/0.99  sup_time_sim_full:                      0.
% 2.36/0.99  sup_time_sim_immed:                     0.
% 2.36/0.99  
% 2.36/0.99  sup_num_of_clauses:                     43
% 2.36/0.99  sup_num_in_active:                      41
% 2.36/0.99  sup_num_in_passive:                     2
% 2.36/0.99  sup_num_of_loops:                       42
% 2.36/0.99  sup_fw_superposition:                   23
% 2.36/0.99  sup_bw_superposition:                   3
% 2.36/0.99  sup_immediate_simplified:               11
% 2.36/0.99  sup_given_eliminated:                   0
% 2.36/0.99  comparisons_done:                       0
% 2.36/0.99  comparisons_avoided:                    0
% 2.36/0.99  
% 2.36/0.99  ------ Simplifications
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  sim_fw_subset_subsumed:                 1
% 2.36/0.99  sim_bw_subset_subsumed:                 0
% 2.36/0.99  sim_fw_subsumed:                        5
% 2.36/0.99  sim_bw_subsumed:                        0
% 2.36/0.99  sim_fw_subsumption_res:                 0
% 2.36/0.99  sim_bw_subsumption_res:                 0
% 2.36/0.99  sim_tautology_del:                      0
% 2.36/0.99  sim_eq_tautology_del:                   0
% 2.36/0.99  sim_eq_res_simp:                        0
% 2.36/0.99  sim_fw_demodulated:                     0
% 2.36/0.99  sim_bw_demodulated:                     2
% 2.36/0.99  sim_light_normalised:                   7
% 2.36/0.99  sim_joinable_taut:                      0
% 2.36/0.99  sim_joinable_simp:                      0
% 2.36/0.99  sim_ac_normalised:                      0
% 2.36/0.99  sim_smt_subsumption:                    0
% 2.36/0.99  
%------------------------------------------------------------------------------
