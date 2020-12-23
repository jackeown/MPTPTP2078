%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:22 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  178 (1060 expanded)
%              Number of clauses        :  115 ( 276 expanded)
%              Number of leaves         :   16 ( 374 expanded)
%              Depth                    :   21
%              Number of atoms          :  737 (8142 expanded)
%              Number of equality atoms :  209 (1172 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f38,f37,f36,f35,f34])).

fof(f62,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1992,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2447,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1992])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_23,c_22,c_20])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(X0_51,sK1)
    | k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51) ),
    inference(subtyping,[status(esa)],[c_736])).

cnf(c_2463,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_2972,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_2447,c_2463])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | sK3 != X2
    | sK0 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_754,plain,
    ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_23,c_22,c_20])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
    inference(renaming,[status(thm)],[c_754])).

cnf(c_1975,plain,
    ( ~ m1_subset_1(X0_51,sK1)
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) ),
    inference(subtyping,[status(esa)],[c_755])).

cnf(c_2464,plain,
    ( m1_subset_1(X0_51,sK1) != iProver_top
    | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_3019,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_2464])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3489,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3019,c_32])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1991,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2448,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1991])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_263,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_2])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | r1_tarski(k2_relat_1(X0_51),X1_52) ),
    inference(subtyping,[status(esa)],[c_264])).

cnf(c_2454,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X1_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_3183,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_2454])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X4),X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_relat_1(X4)
    | X5 != X3
    | X4 != X2
    | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
    | k1_relat_1(X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k7_partfun1(X2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k7_partfun1(X2,X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_597,c_12])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
    | ~ r1_tarski(k2_relat_1(X1_51),X0_52)
    | ~ v1_funct_1(X1_51)
    | v1_xboole_0(X0_52)
    | v1_xboole_0(k1_relat_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | k3_funct_2(k1_relat_1(X1_51),X0_52,X1_51,X0_51) = k7_partfun1(X0_52,X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_2458,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1981])).

cnf(c_2059,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1981])).

cnf(c_1995,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52)))
    | ~ r1_tarski(k2_relat_1(X0_51),X0_52)
    | ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2445,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) = iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

cnf(c_5,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1996,plain,
    ( ~ v1_partfun1(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_xboole_0(X1_52)
    | v1_xboole_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2444,plain,
    ( v1_partfun1(X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_xboole_0(X1_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_2874,plain,
    ( v1_partfun1(X0_51,k1_relat_1(X0_51)) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(X0_52) != iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2444])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_299,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_300,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_310,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_300,c_2])).

cnf(c_1983,plain,
    ( v1_partfun1(X0_51,k1_relat_1(X0_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) ),
    inference(subtyping,[status(esa)],[c_310])).

cnf(c_2456,plain,
    ( v1_partfun1(X0_51,k1_relat_1(X0_51)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_3304,plain,
    ( v1_partfun1(X0_51,k1_relat_1(X0_51)) = iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2456])).

cnf(c_4450,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2458,c_2059,c_2874,c_3304])).

cnf(c_4451,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4450])).

cnf(c_4463,plain,
    ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_4451])).

cnf(c_7,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_279,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_7])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_7,c_4,c_2])).

cnf(c_284,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_1984,plain,
    ( ~ v1_partfun1(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_284])).

cnf(c_2455,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_partfun1(X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_3645,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_partfun1(sK4,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_2455])).

cnf(c_16,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2696,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_2754,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_3814,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_18,c_16,c_2754])).

cnf(c_4469,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4463,c_3814])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2663,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2664,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2663])).

cnf(c_5232,plain,
    ( m1_subset_1(X0_51,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4469,c_25,c_30,c_31,c_2664])).

cnf(c_5233,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5232])).

cnf(c_5242,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3489,c_5233])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X4),X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X4)
    | X5 != X3
    | X4 != X2
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | k1_relat_1(X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k1_funct_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k1_funct_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_629,c_12])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
    | ~ r1_tarski(k2_relat_1(X1_51),X0_52)
    | ~ v1_funct_1(X1_51)
    | v1_xboole_0(k1_relat_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | k3_funct_2(k1_relat_1(X1_51),X0_52,X1_51,X0_51) = k1_funct_1(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_647])).

cnf(c_2459,plain,
    ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
    | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_4547,plain,
    ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_2459])).

cnf(c_4553,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4547,c_3814])).

cnf(c_5110,plain,
    ( m1_subset_1(X0_51,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4553,c_25,c_30,c_31,c_2664])).

cnf(c_5111,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | m1_subset_1(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5110])).

cnf(c_5120,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3489,c_5111])).

cnf(c_8611,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_5242,c_5120])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_686,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_687,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_691,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_24,c_23,c_22,c_20])).

cnf(c_692,plain,
    ( ~ v1_partfun1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
    inference(renaming,[status(thm)],[c_691])).

cnf(c_1978,plain,
    ( ~ v1_partfun1(X0_51,sK0)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
    | ~ m1_subset_1(X1_51,sK1)
    | ~ v1_funct_1(X0_51)
    | k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51)) ),
    inference(subtyping,[status(esa)],[c_692])).

cnf(c_2461,plain,
    ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51))
    | v1_partfun1(X0_51,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
    | m1_subset_1(X1_51,sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_3176,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(X0_51,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_2461])).

cnf(c_33,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3431,plain,
    ( m1_subset_1(X0_51,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3176,c_30,c_33])).

cnf(c_3432,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3431])).

cnf(c_3439,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2447,c_3432])).

cnf(c_3440,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3439,c_2972])).

cnf(c_15,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1994,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2974,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2972,c_1994])).

cnf(c_3495,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3440,c_2974])).

cnf(c_8613,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8611,c_3495])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.20/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.02  
% 3.20/1.02  ------  iProver source info
% 3.20/1.02  
% 3.20/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.02  git: non_committed_changes: false
% 3.20/1.02  git: last_make_outside_of_git: false
% 3.20/1.02  
% 3.20/1.02  ------ 
% 3.20/1.02  
% 3.20/1.02  ------ Input Options
% 3.20/1.02  
% 3.20/1.02  --out_options                           all
% 3.20/1.02  --tptp_safe_out                         true
% 3.20/1.02  --problem_path                          ""
% 3.20/1.02  --include_path                          ""
% 3.20/1.02  --clausifier                            res/vclausify_rel
% 3.20/1.02  --clausifier_options                    --mode clausify
% 3.20/1.02  --stdin                                 false
% 3.20/1.02  --stats_out                             all
% 3.20/1.02  
% 3.20/1.02  ------ General Options
% 3.20/1.02  
% 3.20/1.02  --fof                                   false
% 3.20/1.02  --time_out_real                         305.
% 3.20/1.02  --time_out_virtual                      -1.
% 3.20/1.02  --symbol_type_check                     false
% 3.20/1.02  --clausify_out                          false
% 3.20/1.02  --sig_cnt_out                           false
% 3.20/1.02  --trig_cnt_out                          false
% 3.20/1.02  --trig_cnt_out_tolerance                1.
% 3.20/1.02  --trig_cnt_out_sk_spl                   false
% 3.20/1.02  --abstr_cl_out                          false
% 3.20/1.02  
% 3.20/1.02  ------ Global Options
% 3.20/1.02  
% 3.20/1.02  --schedule                              default
% 3.20/1.02  --add_important_lit                     false
% 3.20/1.02  --prop_solver_per_cl                    1000
% 3.20/1.02  --min_unsat_core                        false
% 3.20/1.02  --soft_assumptions                      false
% 3.20/1.02  --soft_lemma_size                       3
% 3.20/1.02  --prop_impl_unit_size                   0
% 3.20/1.02  --prop_impl_unit                        []
% 3.20/1.02  --share_sel_clauses                     true
% 3.20/1.02  --reset_solvers                         false
% 3.20/1.02  --bc_imp_inh                            [conj_cone]
% 3.20/1.02  --conj_cone_tolerance                   3.
% 3.20/1.02  --extra_neg_conj                        none
% 3.20/1.02  --large_theory_mode                     true
% 3.20/1.02  --prolific_symb_bound                   200
% 3.20/1.02  --lt_threshold                          2000
% 3.20/1.02  --clause_weak_htbl                      true
% 3.20/1.02  --gc_record_bc_elim                     false
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing Options
% 3.20/1.02  
% 3.20/1.02  --preprocessing_flag                    true
% 3.20/1.02  --time_out_prep_mult                    0.1
% 3.20/1.02  --splitting_mode                        input
% 3.20/1.02  --splitting_grd                         true
% 3.20/1.02  --splitting_cvd                         false
% 3.20/1.02  --splitting_cvd_svl                     false
% 3.20/1.02  --splitting_nvd                         32
% 3.20/1.02  --sub_typing                            true
% 3.20/1.02  --prep_gs_sim                           true
% 3.20/1.02  --prep_unflatten                        true
% 3.20/1.02  --prep_res_sim                          true
% 3.20/1.02  --prep_upred                            true
% 3.20/1.02  --prep_sem_filter                       exhaustive
% 3.20/1.02  --prep_sem_filter_out                   false
% 3.20/1.02  --pred_elim                             true
% 3.20/1.02  --res_sim_input                         true
% 3.20/1.02  --eq_ax_congr_red                       true
% 3.20/1.02  --pure_diseq_elim                       true
% 3.20/1.02  --brand_transform                       false
% 3.20/1.02  --non_eq_to_eq                          false
% 3.20/1.02  --prep_def_merge                        true
% 3.20/1.02  --prep_def_merge_prop_impl              false
% 3.20/1.02  --prep_def_merge_mbd                    true
% 3.20/1.02  --prep_def_merge_tr_red                 false
% 3.20/1.02  --prep_def_merge_tr_cl                  false
% 3.20/1.02  --smt_preprocessing                     true
% 3.20/1.02  --smt_ac_axioms                         fast
% 3.20/1.02  --preprocessed_out                      false
% 3.20/1.02  --preprocessed_stats                    false
% 3.20/1.02  
% 3.20/1.02  ------ Abstraction refinement Options
% 3.20/1.02  
% 3.20/1.02  --abstr_ref                             []
% 3.20/1.02  --abstr_ref_prep                        false
% 3.20/1.02  --abstr_ref_until_sat                   false
% 3.20/1.02  --abstr_ref_sig_restrict                funpre
% 3.20/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.02  --abstr_ref_under                       []
% 3.20/1.02  
% 3.20/1.02  ------ SAT Options
% 3.20/1.02  
% 3.20/1.02  --sat_mode                              false
% 3.20/1.02  --sat_fm_restart_options                ""
% 3.20/1.02  --sat_gr_def                            false
% 3.20/1.02  --sat_epr_types                         true
% 3.20/1.02  --sat_non_cyclic_types                  false
% 3.20/1.02  --sat_finite_models                     false
% 3.20/1.02  --sat_fm_lemmas                         false
% 3.20/1.02  --sat_fm_prep                           false
% 3.20/1.02  --sat_fm_uc_incr                        true
% 3.20/1.02  --sat_out_model                         small
% 3.20/1.02  --sat_out_clauses                       false
% 3.20/1.02  
% 3.20/1.02  ------ QBF Options
% 3.20/1.02  
% 3.20/1.02  --qbf_mode                              false
% 3.20/1.02  --qbf_elim_univ                         false
% 3.20/1.02  --qbf_dom_inst                          none
% 3.20/1.02  --qbf_dom_pre_inst                      false
% 3.20/1.02  --qbf_sk_in                             false
% 3.20/1.02  --qbf_pred_elim                         true
% 3.20/1.02  --qbf_split                             512
% 3.20/1.02  
% 3.20/1.02  ------ BMC1 Options
% 3.20/1.02  
% 3.20/1.02  --bmc1_incremental                      false
% 3.20/1.02  --bmc1_axioms                           reachable_all
% 3.20/1.02  --bmc1_min_bound                        0
% 3.20/1.02  --bmc1_max_bound                        -1
% 3.20/1.02  --bmc1_max_bound_default                -1
% 3.20/1.02  --bmc1_symbol_reachability              true
% 3.20/1.02  --bmc1_property_lemmas                  false
% 3.20/1.02  --bmc1_k_induction                      false
% 3.20/1.02  --bmc1_non_equiv_states                 false
% 3.20/1.02  --bmc1_deadlock                         false
% 3.20/1.02  --bmc1_ucm                              false
% 3.20/1.02  --bmc1_add_unsat_core                   none
% 3.20/1.02  --bmc1_unsat_core_children              false
% 3.20/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.02  --bmc1_out_stat                         full
% 3.20/1.02  --bmc1_ground_init                      false
% 3.20/1.02  --bmc1_pre_inst_next_state              false
% 3.20/1.02  --bmc1_pre_inst_state                   false
% 3.20/1.02  --bmc1_pre_inst_reach_state             false
% 3.20/1.02  --bmc1_out_unsat_core                   false
% 3.20/1.02  --bmc1_aig_witness_out                  false
% 3.20/1.02  --bmc1_verbose                          false
% 3.20/1.02  --bmc1_dump_clauses_tptp                false
% 3.20/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.02  --bmc1_dump_file                        -
% 3.20/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.02  --bmc1_ucm_extend_mode                  1
% 3.20/1.02  --bmc1_ucm_init_mode                    2
% 3.20/1.02  --bmc1_ucm_cone_mode                    none
% 3.20/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.02  --bmc1_ucm_relax_model                  4
% 3.20/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.02  --bmc1_ucm_layered_model                none
% 3.20/1.02  --bmc1_ucm_max_lemma_size               10
% 3.20/1.02  
% 3.20/1.02  ------ AIG Options
% 3.20/1.02  
% 3.20/1.02  --aig_mode                              false
% 3.20/1.02  
% 3.20/1.02  ------ Instantiation Options
% 3.20/1.02  
% 3.20/1.02  --instantiation_flag                    true
% 3.20/1.02  --inst_sos_flag                         false
% 3.20/1.02  --inst_sos_phase                        true
% 3.20/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel_side                     num_symb
% 3.20/1.02  --inst_solver_per_active                1400
% 3.20/1.02  --inst_solver_calls_frac                1.
% 3.20/1.02  --inst_passive_queue_type               priority_queues
% 3.20/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.02  --inst_passive_queues_freq              [25;2]
% 3.20/1.02  --inst_dismatching                      true
% 3.20/1.02  --inst_eager_unprocessed_to_passive     true
% 3.20/1.02  --inst_prop_sim_given                   true
% 3.20/1.02  --inst_prop_sim_new                     false
% 3.20/1.02  --inst_subs_new                         false
% 3.20/1.02  --inst_eq_res_simp                      false
% 3.20/1.02  --inst_subs_given                       false
% 3.20/1.02  --inst_orphan_elimination               true
% 3.20/1.02  --inst_learning_loop_flag               true
% 3.20/1.02  --inst_learning_start                   3000
% 3.20/1.02  --inst_learning_factor                  2
% 3.20/1.02  --inst_start_prop_sim_after_learn       3
% 3.20/1.02  --inst_sel_renew                        solver
% 3.20/1.02  --inst_lit_activity_flag                true
% 3.20/1.02  --inst_restr_to_given                   false
% 3.20/1.02  --inst_activity_threshold               500
% 3.20/1.02  --inst_out_proof                        true
% 3.20/1.02  
% 3.20/1.02  ------ Resolution Options
% 3.20/1.02  
% 3.20/1.02  --resolution_flag                       true
% 3.20/1.02  --res_lit_sel                           adaptive
% 3.20/1.02  --res_lit_sel_side                      none
% 3.20/1.02  --res_ordering                          kbo
% 3.20/1.02  --res_to_prop_solver                    active
% 3.20/1.02  --res_prop_simpl_new                    false
% 3.20/1.02  --res_prop_simpl_given                  true
% 3.20/1.02  --res_passive_queue_type                priority_queues
% 3.20/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.02  --res_passive_queues_freq               [15;5]
% 3.20/1.02  --res_forward_subs                      full
% 3.20/1.02  --res_backward_subs                     full
% 3.20/1.02  --res_forward_subs_resolution           true
% 3.20/1.02  --res_backward_subs_resolution          true
% 3.20/1.02  --res_orphan_elimination                true
% 3.20/1.02  --res_time_limit                        2.
% 3.20/1.02  --res_out_proof                         true
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Options
% 3.20/1.02  
% 3.20/1.02  --superposition_flag                    true
% 3.20/1.02  --sup_passive_queue_type                priority_queues
% 3.20/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.02  --demod_completeness_check              fast
% 3.20/1.02  --demod_use_ground                      true
% 3.20/1.02  --sup_to_prop_solver                    passive
% 3.20/1.02  --sup_prop_simpl_new                    true
% 3.20/1.02  --sup_prop_simpl_given                  true
% 3.20/1.02  --sup_fun_splitting                     false
% 3.20/1.02  --sup_smt_interval                      50000
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Simplification Setup
% 3.20/1.02  
% 3.20/1.02  --sup_indices_passive                   []
% 3.20/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_full_bw                           [BwDemod]
% 3.20/1.02  --sup_immed_triv                        [TrivRules]
% 3.20/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_immed_bw_main                     []
% 3.20/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.02  
% 3.20/1.02  ------ Combination Options
% 3.20/1.02  
% 3.20/1.02  --comb_res_mult                         3
% 3.20/1.02  --comb_sup_mult                         2
% 3.20/1.02  --comb_inst_mult                        10
% 3.20/1.02  
% 3.20/1.02  ------ Debug Options
% 3.20/1.02  
% 3.20/1.02  --dbg_backtrace                         false
% 3.20/1.02  --dbg_dump_prop_clauses                 false
% 3.20/1.02  --dbg_dump_prop_clauses_file            -
% 3.20/1.02  --dbg_out_stat                          false
% 3.20/1.02  ------ Parsing...
% 3.20/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.02  ------ Proving...
% 3.20/1.02  ------ Problem Properties 
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  clauses                                 23
% 3.20/1.02  conjectures                             9
% 3.20/1.02  EPR                                     6
% 3.20/1.02  Horn                                    19
% 3.20/1.02  unary                                   9
% 3.20/1.02  binary                                  6
% 3.20/1.02  lits                                    66
% 3.20/1.02  lits eq                                 8
% 3.20/1.02  fd_pure                                 0
% 3.20/1.02  fd_pseudo                               0
% 3.20/1.02  fd_cond                                 0
% 3.20/1.02  fd_pseudo_cond                          1
% 3.20/1.02  AC symbols                              0
% 3.20/1.02  
% 3.20/1.02  ------ Schedule dynamic 5 is on 
% 3.20/1.02  
% 3.20/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  ------ 
% 3.20/1.02  Current options:
% 3.20/1.02  ------ 
% 3.20/1.02  
% 3.20/1.02  ------ Input Options
% 3.20/1.02  
% 3.20/1.02  --out_options                           all
% 3.20/1.02  --tptp_safe_out                         true
% 3.20/1.02  --problem_path                          ""
% 3.20/1.02  --include_path                          ""
% 3.20/1.02  --clausifier                            res/vclausify_rel
% 3.20/1.02  --clausifier_options                    --mode clausify
% 3.20/1.02  --stdin                                 false
% 3.20/1.02  --stats_out                             all
% 3.20/1.02  
% 3.20/1.02  ------ General Options
% 3.20/1.02  
% 3.20/1.02  --fof                                   false
% 3.20/1.02  --time_out_real                         305.
% 3.20/1.02  --time_out_virtual                      -1.
% 3.20/1.02  --symbol_type_check                     false
% 3.20/1.02  --clausify_out                          false
% 3.20/1.02  --sig_cnt_out                           false
% 3.20/1.02  --trig_cnt_out                          false
% 3.20/1.02  --trig_cnt_out_tolerance                1.
% 3.20/1.02  --trig_cnt_out_sk_spl                   false
% 3.20/1.02  --abstr_cl_out                          false
% 3.20/1.02  
% 3.20/1.02  ------ Global Options
% 3.20/1.02  
% 3.20/1.02  --schedule                              default
% 3.20/1.02  --add_important_lit                     false
% 3.20/1.02  --prop_solver_per_cl                    1000
% 3.20/1.02  --min_unsat_core                        false
% 3.20/1.02  --soft_assumptions                      false
% 3.20/1.02  --soft_lemma_size                       3
% 3.20/1.02  --prop_impl_unit_size                   0
% 3.20/1.02  --prop_impl_unit                        []
% 3.20/1.02  --share_sel_clauses                     true
% 3.20/1.02  --reset_solvers                         false
% 3.20/1.02  --bc_imp_inh                            [conj_cone]
% 3.20/1.02  --conj_cone_tolerance                   3.
% 3.20/1.02  --extra_neg_conj                        none
% 3.20/1.02  --large_theory_mode                     true
% 3.20/1.02  --prolific_symb_bound                   200
% 3.20/1.02  --lt_threshold                          2000
% 3.20/1.02  --clause_weak_htbl                      true
% 3.20/1.02  --gc_record_bc_elim                     false
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing Options
% 3.20/1.02  
% 3.20/1.02  --preprocessing_flag                    true
% 3.20/1.02  --time_out_prep_mult                    0.1
% 3.20/1.02  --splitting_mode                        input
% 3.20/1.02  --splitting_grd                         true
% 3.20/1.02  --splitting_cvd                         false
% 3.20/1.02  --splitting_cvd_svl                     false
% 3.20/1.02  --splitting_nvd                         32
% 3.20/1.02  --sub_typing                            true
% 3.20/1.02  --prep_gs_sim                           true
% 3.20/1.02  --prep_unflatten                        true
% 3.20/1.02  --prep_res_sim                          true
% 3.20/1.02  --prep_upred                            true
% 3.20/1.02  --prep_sem_filter                       exhaustive
% 3.20/1.02  --prep_sem_filter_out                   false
% 3.20/1.02  --pred_elim                             true
% 3.20/1.02  --res_sim_input                         true
% 3.20/1.02  --eq_ax_congr_red                       true
% 3.20/1.02  --pure_diseq_elim                       true
% 3.20/1.02  --brand_transform                       false
% 3.20/1.02  --non_eq_to_eq                          false
% 3.20/1.02  --prep_def_merge                        true
% 3.20/1.02  --prep_def_merge_prop_impl              false
% 3.20/1.02  --prep_def_merge_mbd                    true
% 3.20/1.02  --prep_def_merge_tr_red                 false
% 3.20/1.02  --prep_def_merge_tr_cl                  false
% 3.20/1.02  --smt_preprocessing                     true
% 3.20/1.02  --smt_ac_axioms                         fast
% 3.20/1.02  --preprocessed_out                      false
% 3.20/1.02  --preprocessed_stats                    false
% 3.20/1.02  
% 3.20/1.02  ------ Abstraction refinement Options
% 3.20/1.02  
% 3.20/1.02  --abstr_ref                             []
% 3.20/1.02  --abstr_ref_prep                        false
% 3.20/1.02  --abstr_ref_until_sat                   false
% 3.20/1.02  --abstr_ref_sig_restrict                funpre
% 3.20/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.02  --abstr_ref_under                       []
% 3.20/1.02  
% 3.20/1.02  ------ SAT Options
% 3.20/1.02  
% 3.20/1.02  --sat_mode                              false
% 3.20/1.02  --sat_fm_restart_options                ""
% 3.20/1.02  --sat_gr_def                            false
% 3.20/1.02  --sat_epr_types                         true
% 3.20/1.02  --sat_non_cyclic_types                  false
% 3.20/1.02  --sat_finite_models                     false
% 3.20/1.02  --sat_fm_lemmas                         false
% 3.20/1.02  --sat_fm_prep                           false
% 3.20/1.02  --sat_fm_uc_incr                        true
% 3.20/1.02  --sat_out_model                         small
% 3.20/1.02  --sat_out_clauses                       false
% 3.20/1.02  
% 3.20/1.02  ------ QBF Options
% 3.20/1.02  
% 3.20/1.02  --qbf_mode                              false
% 3.20/1.02  --qbf_elim_univ                         false
% 3.20/1.02  --qbf_dom_inst                          none
% 3.20/1.02  --qbf_dom_pre_inst                      false
% 3.20/1.02  --qbf_sk_in                             false
% 3.20/1.02  --qbf_pred_elim                         true
% 3.20/1.02  --qbf_split                             512
% 3.20/1.02  
% 3.20/1.02  ------ BMC1 Options
% 3.20/1.02  
% 3.20/1.02  --bmc1_incremental                      false
% 3.20/1.02  --bmc1_axioms                           reachable_all
% 3.20/1.02  --bmc1_min_bound                        0
% 3.20/1.02  --bmc1_max_bound                        -1
% 3.20/1.02  --bmc1_max_bound_default                -1
% 3.20/1.02  --bmc1_symbol_reachability              true
% 3.20/1.02  --bmc1_property_lemmas                  false
% 3.20/1.02  --bmc1_k_induction                      false
% 3.20/1.02  --bmc1_non_equiv_states                 false
% 3.20/1.02  --bmc1_deadlock                         false
% 3.20/1.02  --bmc1_ucm                              false
% 3.20/1.02  --bmc1_add_unsat_core                   none
% 3.20/1.02  --bmc1_unsat_core_children              false
% 3.20/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.02  --bmc1_out_stat                         full
% 3.20/1.02  --bmc1_ground_init                      false
% 3.20/1.02  --bmc1_pre_inst_next_state              false
% 3.20/1.02  --bmc1_pre_inst_state                   false
% 3.20/1.02  --bmc1_pre_inst_reach_state             false
% 3.20/1.02  --bmc1_out_unsat_core                   false
% 3.20/1.02  --bmc1_aig_witness_out                  false
% 3.20/1.02  --bmc1_verbose                          false
% 3.20/1.02  --bmc1_dump_clauses_tptp                false
% 3.20/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.02  --bmc1_dump_file                        -
% 3.20/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.02  --bmc1_ucm_extend_mode                  1
% 3.20/1.02  --bmc1_ucm_init_mode                    2
% 3.20/1.02  --bmc1_ucm_cone_mode                    none
% 3.20/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.02  --bmc1_ucm_relax_model                  4
% 3.20/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.02  --bmc1_ucm_layered_model                none
% 3.20/1.02  --bmc1_ucm_max_lemma_size               10
% 3.20/1.02  
% 3.20/1.02  ------ AIG Options
% 3.20/1.02  
% 3.20/1.02  --aig_mode                              false
% 3.20/1.02  
% 3.20/1.02  ------ Instantiation Options
% 3.20/1.02  
% 3.20/1.02  --instantiation_flag                    true
% 3.20/1.02  --inst_sos_flag                         false
% 3.20/1.02  --inst_sos_phase                        true
% 3.20/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.02  --inst_lit_sel_side                     none
% 3.20/1.02  --inst_solver_per_active                1400
% 3.20/1.02  --inst_solver_calls_frac                1.
% 3.20/1.02  --inst_passive_queue_type               priority_queues
% 3.20/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.02  --inst_passive_queues_freq              [25;2]
% 3.20/1.02  --inst_dismatching                      true
% 3.20/1.02  --inst_eager_unprocessed_to_passive     true
% 3.20/1.02  --inst_prop_sim_given                   true
% 3.20/1.02  --inst_prop_sim_new                     false
% 3.20/1.02  --inst_subs_new                         false
% 3.20/1.02  --inst_eq_res_simp                      false
% 3.20/1.02  --inst_subs_given                       false
% 3.20/1.02  --inst_orphan_elimination               true
% 3.20/1.02  --inst_learning_loop_flag               true
% 3.20/1.02  --inst_learning_start                   3000
% 3.20/1.02  --inst_learning_factor                  2
% 3.20/1.02  --inst_start_prop_sim_after_learn       3
% 3.20/1.02  --inst_sel_renew                        solver
% 3.20/1.02  --inst_lit_activity_flag                true
% 3.20/1.02  --inst_restr_to_given                   false
% 3.20/1.02  --inst_activity_threshold               500
% 3.20/1.02  --inst_out_proof                        true
% 3.20/1.02  
% 3.20/1.02  ------ Resolution Options
% 3.20/1.02  
% 3.20/1.02  --resolution_flag                       false
% 3.20/1.02  --res_lit_sel                           adaptive
% 3.20/1.02  --res_lit_sel_side                      none
% 3.20/1.02  --res_ordering                          kbo
% 3.20/1.02  --res_to_prop_solver                    active
% 3.20/1.02  --res_prop_simpl_new                    false
% 3.20/1.02  --res_prop_simpl_given                  true
% 3.20/1.02  --res_passive_queue_type                priority_queues
% 3.20/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.02  --res_passive_queues_freq               [15;5]
% 3.20/1.02  --res_forward_subs                      full
% 3.20/1.02  --res_backward_subs                     full
% 3.20/1.02  --res_forward_subs_resolution           true
% 3.20/1.02  --res_backward_subs_resolution          true
% 3.20/1.02  --res_orphan_elimination                true
% 3.20/1.02  --res_time_limit                        2.
% 3.20/1.02  --res_out_proof                         true
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Options
% 3.20/1.02  
% 3.20/1.02  --superposition_flag                    true
% 3.20/1.02  --sup_passive_queue_type                priority_queues
% 3.20/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.02  --demod_completeness_check              fast
% 3.20/1.02  --demod_use_ground                      true
% 3.20/1.02  --sup_to_prop_solver                    passive
% 3.20/1.02  --sup_prop_simpl_new                    true
% 3.20/1.02  --sup_prop_simpl_given                  true
% 3.20/1.02  --sup_fun_splitting                     false
% 3.20/1.02  --sup_smt_interval                      50000
% 3.20/1.02  
% 3.20/1.02  ------ Superposition Simplification Setup
% 3.20/1.02  
% 3.20/1.02  --sup_indices_passive                   []
% 3.20/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_full_bw                           [BwDemod]
% 3.20/1.02  --sup_immed_triv                        [TrivRules]
% 3.20/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_immed_bw_main                     []
% 3.20/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.02  
% 3.20/1.02  ------ Combination Options
% 3.20/1.02  
% 3.20/1.02  --comb_res_mult                         3
% 3.20/1.02  --comb_sup_mult                         2
% 3.20/1.02  --comb_inst_mult                        10
% 3.20/1.02  
% 3.20/1.02  ------ Debug Options
% 3.20/1.02  
% 3.20/1.02  --dbg_backtrace                         false
% 3.20/1.02  --dbg_dump_prop_clauses                 false
% 3.20/1.02  --dbg_dump_prop_clauses_file            -
% 3.20/1.02  --dbg_out_stat                          false
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  ------ Proving...
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  % SZS status Theorem for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02   Resolution empty clause
% 3.20/1.02  
% 3.20/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  fof(f11,conjecture,(
% 3.20/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f12,negated_conjecture,(
% 3.20/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.20/1.02    inference(negated_conjecture,[],[f11])).
% 3.20/1.02  
% 3.20/1.02  fof(f30,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f12])).
% 3.20/1.02  
% 3.20/1.02  fof(f31,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f30])).
% 3.20/1.02  
% 3.20/1.02  fof(f38,plain,(
% 3.20/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f37,plain,(
% 3.20/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f36,plain,(
% 3.20/1.02    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f35,plain,(
% 3.20/1.02    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f34,plain,(
% 3.20/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.20/1.02    introduced(choice_axiom,[])).
% 3.20/1.02  
% 3.20/1.02  fof(f39,plain,(
% 3.20/1.02    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.20/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f38,f37,f36,f35,f34])).
% 3.20/1.02  
% 3.20/1.02  fof(f62,plain,(
% 3.20/1.02    m1_subset_1(sK5,sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f7,axiom,(
% 3.20/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f22,plain,(
% 3.20/1.02    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f7])).
% 3.20/1.02  
% 3.20/1.02  fof(f23,plain,(
% 3.20/1.02    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f22])).
% 3.20/1.02  
% 3.20/1.02  fof(f49,plain,(
% 3.20/1.02    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f23])).
% 3.20/1.02  
% 3.20/1.02  fof(f58,plain,(
% 3.20/1.02    v1_funct_2(sK3,sK1,sK0)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f56,plain,(
% 3.20/1.02    ~v1_xboole_0(sK1)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f57,plain,(
% 3.20/1.02    v1_funct_1(sK3)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f59,plain,(
% 3.20/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f6,axiom,(
% 3.20/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f20,plain,(
% 3.20/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f6])).
% 3.20/1.02  
% 3.20/1.02  fof(f21,plain,(
% 3.20/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f20])).
% 3.20/1.02  
% 3.20/1.02  fof(f48,plain,(
% 3.20/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f21])).
% 3.20/1.02  
% 3.20/1.02  fof(f61,plain,(
% 3.20/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f1,axiom,(
% 3.20/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f13,plain,(
% 3.20/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.20/1.02    inference(ennf_transformation,[],[f1])).
% 3.20/1.02  
% 3.20/1.02  fof(f32,plain,(
% 3.20/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.20/1.02    inference(nnf_transformation,[],[f13])).
% 3.20/1.02  
% 3.20/1.02  fof(f40,plain,(
% 3.20/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f32])).
% 3.20/1.02  
% 3.20/1.02  fof(f3,axiom,(
% 3.20/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f15,plain,(
% 3.20/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/1.02    inference(ennf_transformation,[],[f3])).
% 3.20/1.02  
% 3.20/1.02  fof(f44,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/1.02    inference(cnf_transformation,[],[f15])).
% 3.20/1.02  
% 3.20/1.02  fof(f2,axiom,(
% 3.20/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f14,plain,(
% 3.20/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/1.02    inference(ennf_transformation,[],[f2])).
% 3.20/1.02  
% 3.20/1.02  fof(f42,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/1.02    inference(cnf_transformation,[],[f14])).
% 3.20/1.02  
% 3.20/1.02  fof(f8,axiom,(
% 3.20/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f24,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f8])).
% 3.20/1.02  
% 3.20/1.02  fof(f25,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f24])).
% 3.20/1.02  
% 3.20/1.02  fof(f50,plain,(
% 3.20/1.02    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f25])).
% 3.20/1.02  
% 3.20/1.02  fof(f10,axiom,(
% 3.20/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f28,plain,(
% 3.20/1.02    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.20/1.02    inference(ennf_transformation,[],[f10])).
% 3.20/1.02  
% 3.20/1.02  fof(f29,plain,(
% 3.20/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.20/1.02    inference(flattening,[],[f28])).
% 3.20/1.02  
% 3.20/1.02  fof(f53,plain,(
% 3.20/1.02    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f29])).
% 3.20/1.02  
% 3.20/1.02  fof(f54,plain,(
% 3.20/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f29])).
% 3.20/1.02  
% 3.20/1.02  fof(f4,axiom,(
% 3.20/1.02    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f16,plain,(
% 3.20/1.02    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.20/1.02    inference(ennf_transformation,[],[f4])).
% 3.20/1.02  
% 3.20/1.02  fof(f17,plain,(
% 3.20/1.02    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f16])).
% 3.20/1.02  
% 3.20/1.02  fof(f45,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f17])).
% 3.20/1.02  
% 3.20/1.02  fof(f43,plain,(
% 3.20/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/1.02    inference(cnf_transformation,[],[f15])).
% 3.20/1.02  
% 3.20/1.02  fof(f5,axiom,(
% 3.20/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f18,plain,(
% 3.20/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.20/1.02    inference(ennf_transformation,[],[f5])).
% 3.20/1.02  
% 3.20/1.02  fof(f19,plain,(
% 3.20/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/1.02    inference(flattening,[],[f18])).
% 3.20/1.02  
% 3.20/1.02  fof(f33,plain,(
% 3.20/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/1.02    inference(nnf_transformation,[],[f19])).
% 3.20/1.02  
% 3.20/1.02  fof(f47,plain,(
% 3.20/1.02    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f33])).
% 3.20/1.02  
% 3.20/1.02  fof(f65,plain,(
% 3.20/1.02    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(equality_resolution,[],[f47])).
% 3.20/1.02  
% 3.20/1.02  fof(f46,plain,(
% 3.20/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f33])).
% 3.20/1.02  
% 3.20/1.02  fof(f63,plain,(
% 3.20/1.02    v1_partfun1(sK4,sK0)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f55,plain,(
% 3.20/1.02    ~v1_xboole_0(sK0)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f60,plain,(
% 3.20/1.02    v1_funct_1(sK4)),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  fof(f9,axiom,(
% 3.20/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.20/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.02  
% 3.20/1.02  fof(f26,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.20/1.02    inference(ennf_transformation,[],[f9])).
% 3.20/1.02  
% 3.20/1.02  fof(f27,plain,(
% 3.20/1.02    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.20/1.02    inference(flattening,[],[f26])).
% 3.20/1.02  
% 3.20/1.02  fof(f51,plain,(
% 3.20/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.20/1.02    inference(cnf_transformation,[],[f27])).
% 3.20/1.02  
% 3.20/1.02  fof(f64,plain,(
% 3.20/1.02    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 3.20/1.02    inference(cnf_transformation,[],[f39])).
% 3.20/1.02  
% 3.20/1.02  cnf(c_17,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK5,sK1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1992,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK5,sK1) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2447,plain,
% 3.20/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1992]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_9,plain,
% 3.20/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/1.02      | ~ m1_subset_1(X3,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.20/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_21,negated_conjecture,
% 3.20/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_731,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.20/1.02      | ~ v1_funct_1(X2)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 3.20/1.02      | sK3 != X2
% 3.20/1.02      | sK0 != X3
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_732,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,sK1)
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.20/1.02      | ~ v1_funct_1(sK3)
% 3.20/1.02      | v1_xboole_0(sK1)
% 3.20/1.02      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_731]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_23,negated_conjecture,
% 3.20/1.02      ( ~ v1_xboole_0(sK1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_22,negated_conjecture,
% 3.20/1.02      ( v1_funct_1(sK3) ),
% 3.20/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_20,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.20/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_736,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,sK1)
% 3.20/1.02      | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_732,c_23,c_22,c_20]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1976,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,sK1)
% 3.20/1.02      | k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_736]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2463,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2972,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2447,c_2463]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_8,plain,
% 3.20/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/1.02      | ~ m1_subset_1(X3,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | v1_xboole_0(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_749,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.20/1.02      | m1_subset_1(k3_funct_2(X1,X3,X2,X0),X3)
% 3.20/1.02      | ~ v1_funct_1(X2)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | sK3 != X2
% 3.20/1.02      | sK0 != X3
% 3.20/1.02      | sK1 != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_750,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,sK1)
% 3.20/1.02      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.20/1.02      | ~ v1_funct_1(sK3)
% 3.20/1.02      | v1_xboole_0(sK1) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_749]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_754,plain,
% 3.20/1.02      ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~ m1_subset_1(X0,sK1) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_750,c_23,c_22,c_20]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_755,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_754]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1975,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,sK1)
% 3.20/1.02      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_755]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2464,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,sK1) != iProver_top
% 3.20/1.02      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0_51),sK0) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3019,plain,
% 3.20/1.02      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 3.20/1.02      | m1_subset_1(sK5,sK1) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2972,c_2464]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_32,plain,
% 3.20/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3489,plain,
% 3.20/1.02      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 3.20/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3019,c_32]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_18,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.20/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1991,negated_conjecture,
% 3.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2448,plain,
% 3.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1991]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1,plain,
% 3.20/1.02      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 3.20/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_258,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | r1_tarski(k2_relat_1(X3),X4)
% 3.20/1.02      | ~ v1_relat_1(X3)
% 3.20/1.02      | X0 != X3
% 3.20/1.02      | X2 != X4 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_259,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 3.20/1.02      | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_258]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_263,plain,
% 3.20/1.02      ( r1_tarski(k2_relat_1(X0),X2)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.20/1.02      inference(global_propositional_subsumption,[status(thm)],[c_259,c_2]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_264,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_263]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1985,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X1_52) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_264]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2454,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X1_52) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1985]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3183,plain,
% 3.20/1.02      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2448,c_2454]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_10,plain,
% 3.20/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/1.02      | ~ m1_subset_1(X3,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | v1_xboole_0(X2)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 3.20/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_13,plain,
% 3.20/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_596,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X4),X5)
% 3.20/1.02      | ~ v1_funct_1(X2)
% 3.20/1.02      | ~ v1_funct_1(X4)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | v1_xboole_0(X3)
% 3.20/1.02      | ~ v1_relat_1(X4)
% 3.20/1.02      | X5 != X3
% 3.20/1.02      | X4 != X2
% 3.20/1.02      | k3_funct_2(X1,X3,X2,X0) = k7_partfun1(X3,X2,X0)
% 3.20/1.02      | k1_relat_1(X4) != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_597,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1),X2)
% 3.20/1.02      | ~ v1_funct_1(X1)
% 3.20/1.02      | v1_xboole_0(X2)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1))
% 3.20/1.02      | ~ v1_relat_1(X1)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k7_partfun1(X2,X1,X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_596]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_12,plain,
% 3.20/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_617,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1),X2)
% 3.20/1.02      | ~ v1_funct_1(X1)
% 3.20/1.02      | v1_xboole_0(X2)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1))
% 3.20/1.02      | ~ v1_relat_1(X1)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k7_partfun1(X2,X1,X0) ),
% 3.20/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_597,c_12]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1981,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1_51),X0_52)
% 3.20/1.02      | ~ v1_funct_1(X1_51)
% 3.20/1.02      | v1_xboole_0(X0_52)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1_51))
% 3.20/1.02      | ~ v1_relat_1(X1_51)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1_51),X0_52,X1_51,X0_51) = k7_partfun1(X0_52,X1_51,X0_51) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_617]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2458,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
% 3.20/1.02      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_xboole_0(X0_52) = iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1981]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2059,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
% 3.20/1.02      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_xboole_0(X0_52) = iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1981]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1995,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X0_51),X0_52)
% 3.20/1.02      | ~ v1_funct_1(X0_51)
% 3.20/1.02      | ~ v1_relat_1(X0_51) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2445,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) = iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_xboole_0(X2)
% 3.20/1.02      | v1_xboole_0(X1) ),
% 3.20/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1996,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0_51,X0_52)
% 3.20/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.20/1.02      | ~ v1_xboole_0(X1_52)
% 3.20/1.02      | v1_xboole_0(X0_52) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2444,plain,
% 3.20/1.02      ( v1_partfun1(X0_51,X0_52) != iProver_top
% 3.20/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.20/1.02      | v1_xboole_0(X1_52) != iProver_top
% 3.20/1.02      | v1_xboole_0(X0_52) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2874,plain,
% 3.20/1.02      ( v1_partfun1(X0_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_xboole_0(X0_52) != iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2445,c_2444]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4,plain,
% 3.20/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.20/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_6,plain,
% 3.20/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.20/1.02      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.20/1.02      | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_299,plain,
% 3.20/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.20/1.02      | ~ v1_relat_1(X0)
% 3.20/1.02      | X0 != X1
% 3.20/1.02      | k1_relat_1(X0) != X2 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_300,plain,
% 3.20/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.20/1.02      | ~ v1_relat_1(X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_299]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_310,plain,
% 3.20/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
% 3.20/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_300,c_2]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1983,plain,
% 3.20/1.02      ( v1_partfun1(X0_51,k1_relat_1(X0_51))
% 3.20/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_310]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2456,plain,
% 3.20/1.02      ( v1_partfun1(X0_51,k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_51),X0_52))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3304,plain,
% 3.20/1.02      ( v1_partfun1(X0_51,k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2445,c_2456]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4450,plain,
% 3.20/1.02      ( v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_2458,c_2059,c_2874,c_3304]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4451,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k7_partfun1(X0_52,X0_51,X1_51)
% 3.20/1.02      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_4450]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4463,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
% 3.20/1.02      | v1_funct_1(sK4) != iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 3.20/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3183,c_4451]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_7,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,X1)
% 3.20/1.02      | ~ v4_relat_1(X0,X1)
% 3.20/1.02      | ~ v1_relat_1(X0)
% 3.20/1.02      | k1_relat_1(X0) = X1 ),
% 3.20/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_279,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_relat_1(X0)
% 3.20/1.02      | k1_relat_1(X0) = X1 ),
% 3.20/1.02      inference(resolution,[status(thm)],[c_4,c_7]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_283,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_partfun1(X0,X1)
% 3.20/1.02      | k1_relat_1(X0) = X1 ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_279,c_7,c_4,c_2]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_284,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | k1_relat_1(X0) = X1 ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_283]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1984,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0_51,X0_52)
% 3.20/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.20/1.02      | k1_relat_1(X0_51) = X0_52 ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_284]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2455,plain,
% 3.20/1.02      ( k1_relat_1(X0_51) = X0_52
% 3.20/1.02      | v1_partfun1(X0_51,X0_52) != iProver_top
% 3.20/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3645,plain,
% 3.20/1.02      ( k1_relat_1(sK4) = sK0 | v1_partfun1(sK4,sK0) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2448,c_2455]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_16,negated_conjecture,
% 3.20/1.02      ( v1_partfun1(sK4,sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2696,plain,
% 3.20/1.02      ( ~ v1_partfun1(sK4,sK0)
% 3.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
% 3.20/1.02      | k1_relat_1(sK4) = sK0 ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_1984]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2754,plain,
% 3.20/1.02      ( ~ v1_partfun1(sK4,sK0)
% 3.20/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.20/1.02      | k1_relat_1(sK4) = sK0 ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_2696]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3814,plain,
% 3.20/1.02      ( k1_relat_1(sK4) = sK0 ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_3645,c_18,c_16,c_2754]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4469,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,sK0) != iProver_top
% 3.20/1.02      | v1_funct_1(sK4) != iProver_top
% 3.20/1.02      | v1_xboole_0(sK0) = iProver_top
% 3.20/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.20/1.02      inference(light_normalisation,[status(thm)],[c_4463,c_3814]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_24,negated_conjecture,
% 3.20/1.02      ( ~ v1_xboole_0(sK0) ),
% 3.20/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_25,plain,
% 3.20/1.02      ( v1_xboole_0(sK0) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_19,negated_conjecture,
% 3.20/1.02      ( v1_funct_1(sK4) ),
% 3.20/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_30,plain,
% 3.20/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_31,plain,
% 3.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1997,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.20/1.02      | v1_relat_1(X0_51) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2663,plain,
% 3.20/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.20/1.02      | v1_relat_1(sK4) ),
% 3.20/1.02      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2664,plain,
% 3.20/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.20/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_2663]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5232,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,sK0) != iProver_top
% 3.20/1.02      | k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_4469,c_25,c_30,c_31,c_2664]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5233,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k7_partfun1(sK2,sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,sK0) != iProver_top ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_5232]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5242,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3489,c_5233]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_628,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X4),X5)
% 3.20/1.02      | ~ v1_funct_1(X2)
% 3.20/1.02      | ~ v1_funct_1(X4)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | ~ v1_relat_1(X4)
% 3.20/1.02      | X5 != X3
% 3.20/1.02      | X4 != X2
% 3.20/1.02      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 3.20/1.02      | k1_relat_1(X4) != X1 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_629,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 3.20/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1),X2)
% 3.20/1.02      | ~ v1_funct_1(X1)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1))
% 3.20/1.02      | ~ v1_relat_1(X1)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k1_funct_1(X1,X0) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_628]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_647,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1),X2)
% 3.20/1.02      | ~ v1_funct_1(X1)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1))
% 3.20/1.02      | ~ v1_relat_1(X1)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1),X2,X1,X0) = k1_funct_1(X1,X0) ),
% 3.20/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_629,c_12]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1980,plain,
% 3.20/1.02      ( ~ m1_subset_1(X0_51,k1_relat_1(X1_51))
% 3.20/1.02      | ~ r1_tarski(k2_relat_1(X1_51),X0_52)
% 3.20/1.02      | ~ v1_funct_1(X1_51)
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X1_51))
% 3.20/1.02      | ~ v1_relat_1(X1_51)
% 3.20/1.02      | k3_funct_2(k1_relat_1(X1_51),X0_52,X1_51,X0_51) = k1_funct_1(X1_51,X0_51) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_647]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2459,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(X0_51),X0_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
% 3.20/1.02      | m1_subset_1(X1_51,k1_relat_1(X0_51)) != iProver_top
% 3.20/1.02      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(X0_51)) = iProver_top
% 3.20/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4547,plain,
% 3.20/1.02      ( k3_funct_2(k1_relat_1(sK4),sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,k1_relat_1(sK4)) != iProver_top
% 3.20/1.02      | v1_funct_1(sK4) != iProver_top
% 3.20/1.02      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 3.20/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3183,c_2459]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_4553,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,sK0) != iProver_top
% 3.20/1.02      | v1_funct_1(sK4) != iProver_top
% 3.20/1.02      | v1_xboole_0(sK0) = iProver_top
% 3.20/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.20/1.02      inference(light_normalisation,[status(thm)],[c_4547,c_3814]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5110,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,sK0) != iProver_top
% 3.20/1.02      | k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_4553,c_25,c_30,c_31,c_2664]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5111,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 3.20/1.02      | m1_subset_1(X0_51,sK0) != iProver_top ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_5110]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_5120,plain,
% 3.20/1.02      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_3489,c_5111]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_8611,plain,
% 3.20/1.02      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(light_normalisation,[status(thm)],[c_5242,c_5120]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_11,plain,
% 3.20/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/1.02      | ~ v1_partfun1(X3,X2)
% 3.20/1.02      | ~ m1_subset_1(X4,X1)
% 3.20/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.02      | ~ v1_funct_1(X3)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | v1_xboole_0(X2)
% 3.20/1.02      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X3),X4) = k1_funct_1(X3,k3_funct_2(X1,X2,X0,X4)) ),
% 3.20/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_686,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,X1)
% 3.20/1.02      | ~ m1_subset_1(X2,X3)
% 3.20/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 3.20/1.02      | ~ v1_funct_1(X4)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | v1_xboole_0(X3)
% 3.20/1.02      | v1_xboole_0(X1)
% 3.20/1.02      | k3_funct_2(X3,X5,k8_funct_2(X3,X1,X5,X4,X0),X2) = k1_funct_1(X0,k3_funct_2(X3,X1,X4,X2))
% 3.20/1.02      | sK3 != X4
% 3.20/1.02      | sK0 != X1
% 3.20/1.02      | sK1 != X3 ),
% 3.20/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_687,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,sK1)
% 3.20/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | ~ v1_funct_1(sK3)
% 3.20/1.02      | v1_xboole_0(sK0)
% 3.20/1.02      | v1_xboole_0(sK1)
% 3.20/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 3.20/1.02      inference(unflattening,[status(thm)],[c_686]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_691,plain,
% 3.20/1.02      ( ~ v1_funct_1(X0)
% 3.20/1.02      | ~ v1_partfun1(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,sK1)
% 3.20/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_687,c_24,c_23,c_22,c_20]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_692,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.20/1.02      | ~ m1_subset_1(X2,sK1)
% 3.20/1.02      | ~ v1_funct_1(X0)
% 3.20/1.02      | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_691]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1978,plain,
% 3.20/1.02      ( ~ v1_partfun1(X0_51,sK0)
% 3.20/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
% 3.20/1.02      | ~ m1_subset_1(X1_51,sK1)
% 3.20/1.02      | ~ v1_funct_1(X0_51)
% 3.20/1.02      | k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51)) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_692]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2461,plain,
% 3.20/1.02      ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(X0_51,k3_funct_2(sK1,sK0,sK3,X1_51))
% 3.20/1.02      | v1_partfun1(X0_51,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
% 3.20/1.02      | m1_subset_1(X1_51,sK1) != iProver_top
% 3.20/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_1978]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3176,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
% 3.20/1.02      | v1_partfun1(sK4,sK0) != iProver_top
% 3.20/1.02      | m1_subset_1(X0_51,sK1) != iProver_top
% 3.20/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2448,c_2461]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_33,plain,
% 3.20/1.02      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 3.20/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3431,plain,
% 3.20/1.02      ( m1_subset_1(X0_51,sK1) != iProver_top
% 3.20/1.02      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51)) ),
% 3.20/1.02      inference(global_propositional_subsumption,
% 3.20/1.02                [status(thm)],
% 3.20/1.02                [c_3176,c_30,c_33]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3432,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0_51))
% 3.20/1.02      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 3.20/1.02      inference(renaming,[status(thm)],[c_3431]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3439,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.20/1.02      inference(superposition,[status(thm)],[c_2447,c_3432]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3440,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(light_normalisation,[status(thm)],[c_3439,c_2972]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_15,negated_conjecture,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.20/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_1994,negated_conjecture,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.20/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_2974,plain,
% 3.20/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(demodulation,[status(thm)],[c_2972,c_1994]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_3495,plain,
% 3.20/1.02      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.20/1.02      inference(demodulation,[status(thm)],[c_3440,c_2974]) ).
% 3.20/1.02  
% 3.20/1.02  cnf(c_8613,plain,
% 3.20/1.02      ( $false ),
% 3.20/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_8611,c_3495]) ).
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.02  
% 3.20/1.02  ------                               Statistics
% 3.20/1.02  
% 3.20/1.02  ------ General
% 3.20/1.02  
% 3.20/1.02  abstr_ref_over_cycles:                  0
% 3.20/1.02  abstr_ref_under_cycles:                 0
% 3.20/1.02  gc_basic_clause_elim:                   0
% 3.20/1.02  forced_gc_time:                         0
% 3.20/1.02  parsing_time:                           0.011
% 3.20/1.02  unif_index_cands_time:                  0.
% 3.20/1.02  unif_index_add_time:                    0.
% 3.20/1.02  orderings_time:                         0.
% 3.20/1.02  out_proof_time:                         0.012
% 3.20/1.02  total_time:                             0.277
% 3.20/1.02  num_of_symbols:                         58
% 3.20/1.02  num_of_terms:                           6538
% 3.20/1.02  
% 3.20/1.02  ------ Preprocessing
% 3.20/1.02  
% 3.20/1.02  num_of_splits:                          0
% 3.20/1.02  num_of_split_atoms:                     0
% 3.20/1.02  num_of_reused_defs:                     0
% 3.20/1.02  num_eq_ax_congr_red:                    16
% 3.20/1.02  num_of_sem_filtered_clauses:            1
% 3.20/1.02  num_of_subtypes:                        4
% 3.20/1.02  monotx_restored_types:                  0
% 3.20/1.02  sat_num_of_epr_types:                   0
% 3.20/1.02  sat_num_of_non_cyclic_types:            0
% 3.20/1.02  sat_guarded_non_collapsed_types:        1
% 3.20/1.02  num_pure_diseq_elim:                    0
% 3.20/1.02  simp_replaced_by:                       0
% 3.20/1.02  res_preprocessed:                       128
% 3.20/1.02  prep_upred:                             0
% 3.20/1.02  prep_unflattend:                        88
% 3.20/1.02  smt_new_axioms:                         0
% 3.20/1.02  pred_elim_cands:                        6
% 3.20/1.02  pred_elim:                              3
% 3.20/1.02  pred_elim_cl:                           1
% 3.20/1.02  pred_elim_cycles:                       12
% 3.20/1.02  merged_defs:                            0
% 3.20/1.02  merged_defs_ncl:                        0
% 3.20/1.02  bin_hyper_res:                          0
% 3.20/1.02  prep_cycles:                            4
% 3.20/1.02  pred_elim_time:                         0.033
% 3.20/1.02  splitting_time:                         0.
% 3.20/1.02  sem_filter_time:                        0.
% 3.20/1.02  monotx_time:                            0.
% 3.20/1.02  subtype_inf_time:                       0.
% 3.20/1.02  
% 3.20/1.02  ------ Problem properties
% 3.20/1.02  
% 3.20/1.02  clauses:                                23
% 3.20/1.02  conjectures:                            9
% 3.20/1.02  epr:                                    6
% 3.20/1.02  horn:                                   19
% 3.20/1.02  ground:                                 9
% 3.20/1.02  unary:                                  9
% 3.20/1.02  binary:                                 6
% 3.20/1.02  lits:                                   66
% 3.20/1.02  lits_eq:                                8
% 3.20/1.02  fd_pure:                                0
% 3.20/1.02  fd_pseudo:                              0
% 3.20/1.02  fd_cond:                                0
% 3.20/1.02  fd_pseudo_cond:                         1
% 3.20/1.02  ac_symbols:                             0
% 3.20/1.02  
% 3.20/1.02  ------ Propositional Solver
% 3.20/1.02  
% 3.20/1.02  prop_solver_calls:                      30
% 3.20/1.02  prop_fast_solver_calls:                 1748
% 3.20/1.02  smt_solver_calls:                       0
% 3.20/1.02  smt_fast_solver_calls:                  0
% 3.20/1.02  prop_num_of_clauses:                    2324
% 3.20/1.02  prop_preprocess_simplified:             6909
% 3.20/1.02  prop_fo_subsumed:                       97
% 3.20/1.02  prop_solver_time:                       0.
% 3.20/1.02  smt_solver_time:                        0.
% 3.20/1.02  smt_fast_solver_time:                   0.
% 3.20/1.02  prop_fast_solver_time:                  0.
% 3.20/1.02  prop_unsat_core_time:                   0.
% 3.20/1.02  
% 3.20/1.02  ------ QBF
% 3.20/1.02  
% 3.20/1.02  qbf_q_res:                              0
% 3.20/1.02  qbf_num_tautologies:                    0
% 3.20/1.02  qbf_prep_cycles:                        0
% 3.20/1.02  
% 3.20/1.02  ------ BMC1
% 3.20/1.02  
% 3.20/1.02  bmc1_current_bound:                     -1
% 3.20/1.02  bmc1_last_solved_bound:                 -1
% 3.20/1.02  bmc1_unsat_core_size:                   -1
% 3.20/1.02  bmc1_unsat_core_parents_size:           -1
% 3.20/1.02  bmc1_merge_next_fun:                    0
% 3.20/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.02  
% 3.20/1.02  ------ Instantiation
% 3.20/1.02  
% 3.20/1.02  inst_num_of_clauses:                    699
% 3.20/1.02  inst_num_in_passive:                    217
% 3.20/1.02  inst_num_in_active:                     454
% 3.20/1.02  inst_num_in_unprocessed:                28
% 3.20/1.02  inst_num_of_loops:                      470
% 3.20/1.02  inst_num_of_learning_restarts:          0
% 3.20/1.02  inst_num_moves_active_passive:          12
% 3.20/1.02  inst_lit_activity:                      0
% 3.20/1.02  inst_lit_activity_moves:                0
% 3.20/1.02  inst_num_tautologies:                   0
% 3.20/1.02  inst_num_prop_implied:                  0
% 3.20/1.02  inst_num_existing_simplified:           0
% 3.20/1.02  inst_num_eq_res_simplified:             0
% 3.20/1.02  inst_num_child_elim:                    0
% 3.20/1.02  inst_num_of_dismatching_blockings:      238
% 3.20/1.02  inst_num_of_non_proper_insts:           793
% 3.20/1.02  inst_num_of_duplicates:                 0
% 3.20/1.02  inst_inst_num_from_inst_to_res:         0
% 3.20/1.02  inst_dismatching_checking_time:         0.
% 3.20/1.02  
% 3.20/1.02  ------ Resolution
% 3.20/1.02  
% 3.20/1.02  res_num_of_clauses:                     0
% 3.20/1.02  res_num_in_passive:                     0
% 3.20/1.02  res_num_in_active:                      0
% 3.20/1.02  res_num_of_loops:                       132
% 3.20/1.02  res_forward_subset_subsumed:            118
% 3.20/1.02  res_backward_subset_subsumed:           0
% 3.20/1.02  res_forward_subsumed:                   0
% 3.20/1.02  res_backward_subsumed:                  0
% 3.20/1.02  res_forward_subsumption_resolution:     5
% 3.20/1.02  res_backward_subsumption_resolution:    0
% 3.20/1.02  res_clause_to_clause_subsumption:       931
% 3.20/1.02  res_orphan_elimination:                 0
% 3.20/1.02  res_tautology_del:                      150
% 3.20/1.02  res_num_eq_res_simplified:              0
% 3.20/1.02  res_num_sel_changes:                    0
% 3.20/1.02  res_moves_from_active_to_pass:          0
% 3.20/1.02  
% 3.20/1.02  ------ Superposition
% 3.20/1.02  
% 3.20/1.02  sup_time_total:                         0.
% 3.20/1.02  sup_time_generating:                    0.
% 3.20/1.02  sup_time_sim_full:                      0.
% 3.20/1.02  sup_time_sim_immed:                     0.
% 3.20/1.02  
% 3.20/1.02  sup_num_of_clauses:                     131
% 3.20/1.02  sup_num_in_active:                      89
% 3.20/1.02  sup_num_in_passive:                     42
% 3.20/1.02  sup_num_of_loops:                       92
% 3.20/1.02  sup_fw_superposition:                   93
% 3.20/1.02  sup_bw_superposition:                   47
% 3.20/1.02  sup_immediate_simplified:               44
% 3.20/1.02  sup_given_eliminated:                   0
% 3.20/1.02  comparisons_done:                       0
% 3.20/1.02  comparisons_avoided:                    0
% 3.20/1.02  
% 3.20/1.02  ------ Simplifications
% 3.20/1.02  
% 3.20/1.02  
% 3.20/1.02  sim_fw_subset_subsumed:                 11
% 3.20/1.02  sim_bw_subset_subsumed:                 0
% 3.20/1.02  sim_fw_subsumed:                        8
% 3.20/1.02  sim_bw_subsumed:                        0
% 3.20/1.02  sim_fw_subsumption_res:                 11
% 3.20/1.02  sim_bw_subsumption_res:                 0
% 3.20/1.02  sim_tautology_del:                      3
% 3.20/1.02  sim_eq_tautology_del:                   1
% 3.20/1.02  sim_eq_res_simp:                        0
% 3.20/1.02  sim_fw_demodulated:                     0
% 3.20/1.02  sim_bw_demodulated:                     3
% 3.20/1.02  sim_light_normalised:                   34
% 3.20/1.02  sim_joinable_taut:                      0
% 3.20/1.02  sim_joinable_simp:                      0
% 3.20/1.02  sim_ac_normalised:                      0
% 3.20/1.02  sim_smt_subsumption:                    0
% 3.20/1.02  
%------------------------------------------------------------------------------
