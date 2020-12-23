%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:20 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 615 expanded)
%              Number of clauses        :  111 ( 175 expanded)
%              Number of leaves         :   22 ( 223 expanded)
%              Depth                    :   16
%              Number of atoms          :  661 (4697 expanded)
%              Number of equality atoms :  231 ( 759 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
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
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5))
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
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5))
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
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
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
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5))
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
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
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
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5))
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
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
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

fof(f67,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1117,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1790,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_5760,plain,
    ( r1_tarski(sK1,X0)
    | ~ r1_tarski(k1_xboole_0,X1)
    | X0 != X1
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_7370,plain,
    ( r1_tarski(sK1,sK5)
    | ~ r1_tarski(k1_xboole_0,X0)
    | sK5 != X0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5760])).

cnf(c_9361,plain,
    ( r1_tarski(sK1,sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 != sK5
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7370])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6821,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1548,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1547,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1545,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1553,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_1550,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2885,plain,
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
    inference(superposition,[status(thm)],[c_1553,c_1550])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1551,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_1552,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5416,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2885,c_1551,c_1552])).

cnf(c_5422,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_5416])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5584,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5422,c_29,c_30,c_31])).

cnf(c_5595,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_5584])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5717,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5595,c_33])).

cnf(c_5718,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5717])).

cnf(c_5725,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1548,c_5718])).

cnf(c_2352,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1550])).

cnf(c_2595,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_29,c_30,c_31])).

cnf(c_2603,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1548,c_2595])).

cnf(c_18,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2745,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2603,c_18])).

cnf(c_5727,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_5725,c_2745])).

cnf(c_1116,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2486,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_3027,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_4912,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_2754,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3),X2)
    | X1 != X2
    | X0 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_3420,plain,
    ( r1_tarski(k2_relset_1(sK1,sK0,sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | X0 != X1
    | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2754])).

cnf(c_3779,plain,
    ( r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_3420])).

cnf(c_3780,plain,
    ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK4) != X0
    | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3779])).

cnf(c_3782,plain,
    ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK4) != sK0
    | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3780])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2332,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1557])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1934,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1935,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2117,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2118,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_2525,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2332,c_34,c_1935,c_2118])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_377,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_378,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_378])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_1113,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_395])).

cnf(c_1537,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_2530,plain,
    ( k1_relat_1(sK4) = sK0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_1537])).

cnf(c_1143,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_1112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_395])).

cnf(c_1538,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_2124,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1538])).

cnf(c_3674,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2530,c_34,c_1143,c_1935,c_2118,c_2124])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1555,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2138,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1547,c_1555])).

cnf(c_3677,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_3674,c_2138])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1859,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X4,X0,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2030,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relset_1(X0,X1,sK3),k1_relset_1(X1,X3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,sK3,sK4),X2) = k1_funct_1(sK4,k1_funct_1(sK3,X2))
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_2191,plain,
    ( ~ v1_funct_2(sK3,sK1,X0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relset_1(X0,X1,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(X0)
    | k1_funct_1(k8_funct_2(sK1,X0,X1,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_2379,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_2380,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_4])).

cnf(c_1539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_2262,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1539])).

cnf(c_1115,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2237,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_2126,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2127,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_1937,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1938,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_1886,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1787,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(sK1,sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9361,c_6821,c_5727,c_4912,c_3782,c_3677,c_2380,c_2262,c_2237,c_2127,c_1938,c_1886,c_1787,c_1758,c_35,c_20,c_34,c_33,c_32,c_23,c_31,c_30,c_26,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:03:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.05/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.03  
% 2.05/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/1.03  
% 2.05/1.03  ------  iProver source info
% 2.05/1.03  
% 2.05/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.05/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/1.03  git: non_committed_changes: false
% 2.05/1.03  git: last_make_outside_of_git: false
% 2.05/1.03  
% 2.05/1.03  ------ 
% 2.05/1.03  
% 2.05/1.03  ------ Input Options
% 2.05/1.03  
% 2.05/1.03  --out_options                           all
% 2.05/1.03  --tptp_safe_out                         true
% 2.05/1.03  --problem_path                          ""
% 2.05/1.03  --include_path                          ""
% 2.05/1.03  --clausifier                            res/vclausify_rel
% 2.05/1.03  --clausifier_options                    --mode clausify
% 2.05/1.03  --stdin                                 false
% 2.05/1.03  --stats_out                             all
% 2.05/1.03  
% 2.05/1.03  ------ General Options
% 2.05/1.03  
% 2.05/1.03  --fof                                   false
% 2.05/1.03  --time_out_real                         305.
% 2.05/1.03  --time_out_virtual                      -1.
% 2.05/1.03  --symbol_type_check                     false
% 2.05/1.03  --clausify_out                          false
% 2.05/1.03  --sig_cnt_out                           false
% 2.05/1.03  --trig_cnt_out                          false
% 2.05/1.03  --trig_cnt_out_tolerance                1.
% 2.05/1.03  --trig_cnt_out_sk_spl                   false
% 2.05/1.03  --abstr_cl_out                          false
% 2.05/1.03  
% 2.05/1.03  ------ Global Options
% 2.05/1.03  
% 2.05/1.03  --schedule                              default
% 2.05/1.03  --add_important_lit                     false
% 2.05/1.03  --prop_solver_per_cl                    1000
% 2.05/1.03  --min_unsat_core                        false
% 2.05/1.03  --soft_assumptions                      false
% 2.05/1.03  --soft_lemma_size                       3
% 2.05/1.03  --prop_impl_unit_size                   0
% 2.05/1.03  --prop_impl_unit                        []
% 2.05/1.03  --share_sel_clauses                     true
% 2.05/1.03  --reset_solvers                         false
% 2.05/1.03  --bc_imp_inh                            [conj_cone]
% 2.05/1.03  --conj_cone_tolerance                   3.
% 2.05/1.03  --extra_neg_conj                        none
% 2.05/1.03  --large_theory_mode                     true
% 2.05/1.03  --prolific_symb_bound                   200
% 2.05/1.03  --lt_threshold                          2000
% 2.05/1.03  --clause_weak_htbl                      true
% 2.05/1.03  --gc_record_bc_elim                     false
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing Options
% 2.05/1.03  
% 2.05/1.03  --preprocessing_flag                    true
% 2.05/1.03  --time_out_prep_mult                    0.1
% 2.05/1.03  --splitting_mode                        input
% 2.05/1.03  --splitting_grd                         true
% 2.05/1.03  --splitting_cvd                         false
% 2.05/1.03  --splitting_cvd_svl                     false
% 2.05/1.03  --splitting_nvd                         32
% 2.05/1.03  --sub_typing                            true
% 2.05/1.03  --prep_gs_sim                           true
% 2.05/1.03  --prep_unflatten                        true
% 2.05/1.03  --prep_res_sim                          true
% 2.05/1.03  --prep_upred                            true
% 2.05/1.03  --prep_sem_filter                       exhaustive
% 2.05/1.03  --prep_sem_filter_out                   false
% 2.05/1.03  --pred_elim                             true
% 2.05/1.03  --res_sim_input                         true
% 2.05/1.03  --eq_ax_congr_red                       true
% 2.05/1.03  --pure_diseq_elim                       true
% 2.05/1.03  --brand_transform                       false
% 2.05/1.03  --non_eq_to_eq                          false
% 2.05/1.03  --prep_def_merge                        true
% 2.05/1.03  --prep_def_merge_prop_impl              false
% 2.05/1.03  --prep_def_merge_mbd                    true
% 2.05/1.03  --prep_def_merge_tr_red                 false
% 2.05/1.03  --prep_def_merge_tr_cl                  false
% 2.05/1.03  --smt_preprocessing                     true
% 2.05/1.03  --smt_ac_axioms                         fast
% 2.05/1.03  --preprocessed_out                      false
% 2.05/1.03  --preprocessed_stats                    false
% 2.05/1.03  
% 2.05/1.03  ------ Abstraction refinement Options
% 2.05/1.03  
% 2.05/1.03  --abstr_ref                             []
% 2.05/1.03  --abstr_ref_prep                        false
% 2.05/1.03  --abstr_ref_until_sat                   false
% 2.05/1.03  --abstr_ref_sig_restrict                funpre
% 2.05/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.03  --abstr_ref_under                       []
% 2.05/1.03  
% 2.05/1.03  ------ SAT Options
% 2.05/1.03  
% 2.05/1.03  --sat_mode                              false
% 2.05/1.03  --sat_fm_restart_options                ""
% 2.05/1.03  --sat_gr_def                            false
% 2.05/1.03  --sat_epr_types                         true
% 2.05/1.03  --sat_non_cyclic_types                  false
% 2.05/1.03  --sat_finite_models                     false
% 2.05/1.03  --sat_fm_lemmas                         false
% 2.05/1.03  --sat_fm_prep                           false
% 2.05/1.03  --sat_fm_uc_incr                        true
% 2.05/1.03  --sat_out_model                         small
% 2.05/1.03  --sat_out_clauses                       false
% 2.05/1.03  
% 2.05/1.03  ------ QBF Options
% 2.05/1.03  
% 2.05/1.03  --qbf_mode                              false
% 2.05/1.03  --qbf_elim_univ                         false
% 2.05/1.03  --qbf_dom_inst                          none
% 2.05/1.03  --qbf_dom_pre_inst                      false
% 2.05/1.03  --qbf_sk_in                             false
% 2.05/1.03  --qbf_pred_elim                         true
% 2.05/1.03  --qbf_split                             512
% 2.05/1.03  
% 2.05/1.03  ------ BMC1 Options
% 2.05/1.03  
% 2.05/1.03  --bmc1_incremental                      false
% 2.05/1.03  --bmc1_axioms                           reachable_all
% 2.05/1.03  --bmc1_min_bound                        0
% 2.05/1.03  --bmc1_max_bound                        -1
% 2.05/1.03  --bmc1_max_bound_default                -1
% 2.05/1.03  --bmc1_symbol_reachability              true
% 2.05/1.03  --bmc1_property_lemmas                  false
% 2.05/1.03  --bmc1_k_induction                      false
% 2.05/1.03  --bmc1_non_equiv_states                 false
% 2.05/1.03  --bmc1_deadlock                         false
% 2.05/1.03  --bmc1_ucm                              false
% 2.05/1.03  --bmc1_add_unsat_core                   none
% 2.05/1.03  --bmc1_unsat_core_children              false
% 2.05/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.03  --bmc1_out_stat                         full
% 2.05/1.03  --bmc1_ground_init                      false
% 2.05/1.03  --bmc1_pre_inst_next_state              false
% 2.05/1.03  --bmc1_pre_inst_state                   false
% 2.05/1.03  --bmc1_pre_inst_reach_state             false
% 2.05/1.03  --bmc1_out_unsat_core                   false
% 2.05/1.03  --bmc1_aig_witness_out                  false
% 2.05/1.03  --bmc1_verbose                          false
% 2.05/1.03  --bmc1_dump_clauses_tptp                false
% 2.05/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.03  --bmc1_dump_file                        -
% 2.05/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.03  --bmc1_ucm_extend_mode                  1
% 2.05/1.03  --bmc1_ucm_init_mode                    2
% 2.05/1.03  --bmc1_ucm_cone_mode                    none
% 2.05/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.03  --bmc1_ucm_relax_model                  4
% 2.05/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.03  --bmc1_ucm_layered_model                none
% 2.05/1.03  --bmc1_ucm_max_lemma_size               10
% 2.05/1.03  
% 2.05/1.03  ------ AIG Options
% 2.05/1.03  
% 2.05/1.03  --aig_mode                              false
% 2.05/1.03  
% 2.05/1.03  ------ Instantiation Options
% 2.05/1.03  
% 2.05/1.03  --instantiation_flag                    true
% 2.05/1.03  --inst_sos_flag                         false
% 2.05/1.03  --inst_sos_phase                        true
% 2.05/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.03  --inst_lit_sel_side                     num_symb
% 2.05/1.03  --inst_solver_per_active                1400
% 2.05/1.03  --inst_solver_calls_frac                1.
% 2.05/1.03  --inst_passive_queue_type               priority_queues
% 2.05/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.03  --inst_passive_queues_freq              [25;2]
% 2.05/1.03  --inst_dismatching                      true
% 2.05/1.03  --inst_eager_unprocessed_to_passive     true
% 2.05/1.03  --inst_prop_sim_given                   true
% 2.05/1.03  --inst_prop_sim_new                     false
% 2.05/1.03  --inst_subs_new                         false
% 2.05/1.03  --inst_eq_res_simp                      false
% 2.05/1.03  --inst_subs_given                       false
% 2.05/1.03  --inst_orphan_elimination               true
% 2.05/1.03  --inst_learning_loop_flag               true
% 2.05/1.03  --inst_learning_start                   3000
% 2.05/1.03  --inst_learning_factor                  2
% 2.05/1.03  --inst_start_prop_sim_after_learn       3
% 2.05/1.03  --inst_sel_renew                        solver
% 2.05/1.03  --inst_lit_activity_flag                true
% 2.05/1.03  --inst_restr_to_given                   false
% 2.05/1.03  --inst_activity_threshold               500
% 2.05/1.03  --inst_out_proof                        true
% 2.05/1.03  
% 2.05/1.03  ------ Resolution Options
% 2.05/1.03  
% 2.05/1.03  --resolution_flag                       true
% 2.05/1.03  --res_lit_sel                           adaptive
% 2.05/1.03  --res_lit_sel_side                      none
% 2.05/1.03  --res_ordering                          kbo
% 2.05/1.03  --res_to_prop_solver                    active
% 2.05/1.03  --res_prop_simpl_new                    false
% 2.05/1.03  --res_prop_simpl_given                  true
% 2.05/1.03  --res_passive_queue_type                priority_queues
% 2.05/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.03  --res_passive_queues_freq               [15;5]
% 2.05/1.03  --res_forward_subs                      full
% 2.05/1.03  --res_backward_subs                     full
% 2.05/1.03  --res_forward_subs_resolution           true
% 2.05/1.03  --res_backward_subs_resolution          true
% 2.05/1.03  --res_orphan_elimination                true
% 2.05/1.03  --res_time_limit                        2.
% 2.05/1.03  --res_out_proof                         true
% 2.05/1.03  
% 2.05/1.03  ------ Superposition Options
% 2.05/1.03  
% 2.05/1.03  --superposition_flag                    true
% 2.05/1.03  --sup_passive_queue_type                priority_queues
% 2.05/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.03  --demod_completeness_check              fast
% 2.05/1.03  --demod_use_ground                      true
% 2.05/1.03  --sup_to_prop_solver                    passive
% 2.05/1.03  --sup_prop_simpl_new                    true
% 2.05/1.03  --sup_prop_simpl_given                  true
% 2.05/1.03  --sup_fun_splitting                     false
% 2.05/1.03  --sup_smt_interval                      50000
% 2.05/1.03  
% 2.05/1.03  ------ Superposition Simplification Setup
% 2.05/1.03  
% 2.05/1.03  --sup_indices_passive                   []
% 2.05/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_full_bw                           [BwDemod]
% 2.05/1.03  --sup_immed_triv                        [TrivRules]
% 2.05/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_immed_bw_main                     []
% 2.05/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.03  
% 2.05/1.03  ------ Combination Options
% 2.05/1.03  
% 2.05/1.03  --comb_res_mult                         3
% 2.05/1.03  --comb_sup_mult                         2
% 2.05/1.03  --comb_inst_mult                        10
% 2.05/1.03  
% 2.05/1.03  ------ Debug Options
% 2.05/1.03  
% 2.05/1.03  --dbg_backtrace                         false
% 2.05/1.03  --dbg_dump_prop_clauses                 false
% 2.05/1.03  --dbg_dump_prop_clauses_file            -
% 2.05/1.03  --dbg_out_stat                          false
% 2.05/1.03  ------ Parsing...
% 2.05/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/1.03  ------ Proving...
% 2.05/1.03  ------ Problem Properties 
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  clauses                                 23
% 2.05/1.03  conjectures                             9
% 2.05/1.03  EPR                                     8
% 2.05/1.03  Horn                                    20
% 2.05/1.03  unary                                   11
% 2.05/1.03  binary                                  3
% 2.05/1.03  lits                                    63
% 2.05/1.03  lits eq                                 7
% 2.05/1.03  fd_pure                                 0
% 2.05/1.03  fd_pseudo                               0
% 2.05/1.03  fd_cond                                 1
% 2.05/1.03  fd_pseudo_cond                          0
% 2.05/1.03  AC symbols                              0
% 2.05/1.03  
% 2.05/1.03  ------ Schedule dynamic 5 is on 
% 2.05/1.03  
% 2.05/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  ------ 
% 2.05/1.03  Current options:
% 2.05/1.03  ------ 
% 2.05/1.03  
% 2.05/1.03  ------ Input Options
% 2.05/1.03  
% 2.05/1.03  --out_options                           all
% 2.05/1.03  --tptp_safe_out                         true
% 2.05/1.03  --problem_path                          ""
% 2.05/1.03  --include_path                          ""
% 2.05/1.03  --clausifier                            res/vclausify_rel
% 2.05/1.03  --clausifier_options                    --mode clausify
% 2.05/1.03  --stdin                                 false
% 2.05/1.03  --stats_out                             all
% 2.05/1.03  
% 2.05/1.03  ------ General Options
% 2.05/1.03  
% 2.05/1.03  --fof                                   false
% 2.05/1.03  --time_out_real                         305.
% 2.05/1.03  --time_out_virtual                      -1.
% 2.05/1.03  --symbol_type_check                     false
% 2.05/1.03  --clausify_out                          false
% 2.05/1.03  --sig_cnt_out                           false
% 2.05/1.03  --trig_cnt_out                          false
% 2.05/1.03  --trig_cnt_out_tolerance                1.
% 2.05/1.03  --trig_cnt_out_sk_spl                   false
% 2.05/1.03  --abstr_cl_out                          false
% 2.05/1.03  
% 2.05/1.03  ------ Global Options
% 2.05/1.03  
% 2.05/1.03  --schedule                              default
% 2.05/1.03  --add_important_lit                     false
% 2.05/1.03  --prop_solver_per_cl                    1000
% 2.05/1.03  --min_unsat_core                        false
% 2.05/1.03  --soft_assumptions                      false
% 2.05/1.03  --soft_lemma_size                       3
% 2.05/1.03  --prop_impl_unit_size                   0
% 2.05/1.03  --prop_impl_unit                        []
% 2.05/1.03  --share_sel_clauses                     true
% 2.05/1.03  --reset_solvers                         false
% 2.05/1.03  --bc_imp_inh                            [conj_cone]
% 2.05/1.03  --conj_cone_tolerance                   3.
% 2.05/1.03  --extra_neg_conj                        none
% 2.05/1.03  --large_theory_mode                     true
% 2.05/1.03  --prolific_symb_bound                   200
% 2.05/1.03  --lt_threshold                          2000
% 2.05/1.03  --clause_weak_htbl                      true
% 2.05/1.03  --gc_record_bc_elim                     false
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing Options
% 2.05/1.03  
% 2.05/1.03  --preprocessing_flag                    true
% 2.05/1.03  --time_out_prep_mult                    0.1
% 2.05/1.03  --splitting_mode                        input
% 2.05/1.03  --splitting_grd                         true
% 2.05/1.03  --splitting_cvd                         false
% 2.05/1.03  --splitting_cvd_svl                     false
% 2.05/1.03  --splitting_nvd                         32
% 2.05/1.03  --sub_typing                            true
% 2.05/1.03  --prep_gs_sim                           true
% 2.05/1.03  --prep_unflatten                        true
% 2.05/1.03  --prep_res_sim                          true
% 2.05/1.03  --prep_upred                            true
% 2.05/1.03  --prep_sem_filter                       exhaustive
% 2.05/1.03  --prep_sem_filter_out                   false
% 2.05/1.03  --pred_elim                             true
% 2.05/1.03  --res_sim_input                         true
% 2.05/1.03  --eq_ax_congr_red                       true
% 2.05/1.03  --pure_diseq_elim                       true
% 2.05/1.03  --brand_transform                       false
% 2.05/1.03  --non_eq_to_eq                          false
% 2.05/1.03  --prep_def_merge                        true
% 2.05/1.03  --prep_def_merge_prop_impl              false
% 2.05/1.03  --prep_def_merge_mbd                    true
% 2.05/1.03  --prep_def_merge_tr_red                 false
% 2.05/1.03  --prep_def_merge_tr_cl                  false
% 2.05/1.03  --smt_preprocessing                     true
% 2.05/1.03  --smt_ac_axioms                         fast
% 2.05/1.03  --preprocessed_out                      false
% 2.05/1.03  --preprocessed_stats                    false
% 2.05/1.03  
% 2.05/1.03  ------ Abstraction refinement Options
% 2.05/1.03  
% 2.05/1.03  --abstr_ref                             []
% 2.05/1.03  --abstr_ref_prep                        false
% 2.05/1.03  --abstr_ref_until_sat                   false
% 2.05/1.03  --abstr_ref_sig_restrict                funpre
% 2.05/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.03  --abstr_ref_under                       []
% 2.05/1.03  
% 2.05/1.03  ------ SAT Options
% 2.05/1.03  
% 2.05/1.03  --sat_mode                              false
% 2.05/1.03  --sat_fm_restart_options                ""
% 2.05/1.03  --sat_gr_def                            false
% 2.05/1.03  --sat_epr_types                         true
% 2.05/1.03  --sat_non_cyclic_types                  false
% 2.05/1.03  --sat_finite_models                     false
% 2.05/1.03  --sat_fm_lemmas                         false
% 2.05/1.03  --sat_fm_prep                           false
% 2.05/1.03  --sat_fm_uc_incr                        true
% 2.05/1.03  --sat_out_model                         small
% 2.05/1.03  --sat_out_clauses                       false
% 2.05/1.03  
% 2.05/1.03  ------ QBF Options
% 2.05/1.03  
% 2.05/1.03  --qbf_mode                              false
% 2.05/1.03  --qbf_elim_univ                         false
% 2.05/1.03  --qbf_dom_inst                          none
% 2.05/1.03  --qbf_dom_pre_inst                      false
% 2.05/1.03  --qbf_sk_in                             false
% 2.05/1.03  --qbf_pred_elim                         true
% 2.05/1.03  --qbf_split                             512
% 2.05/1.03  
% 2.05/1.03  ------ BMC1 Options
% 2.05/1.03  
% 2.05/1.03  --bmc1_incremental                      false
% 2.05/1.03  --bmc1_axioms                           reachable_all
% 2.05/1.03  --bmc1_min_bound                        0
% 2.05/1.03  --bmc1_max_bound                        -1
% 2.05/1.03  --bmc1_max_bound_default                -1
% 2.05/1.03  --bmc1_symbol_reachability              true
% 2.05/1.03  --bmc1_property_lemmas                  false
% 2.05/1.03  --bmc1_k_induction                      false
% 2.05/1.03  --bmc1_non_equiv_states                 false
% 2.05/1.03  --bmc1_deadlock                         false
% 2.05/1.03  --bmc1_ucm                              false
% 2.05/1.03  --bmc1_add_unsat_core                   none
% 2.05/1.03  --bmc1_unsat_core_children              false
% 2.05/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.03  --bmc1_out_stat                         full
% 2.05/1.03  --bmc1_ground_init                      false
% 2.05/1.03  --bmc1_pre_inst_next_state              false
% 2.05/1.03  --bmc1_pre_inst_state                   false
% 2.05/1.03  --bmc1_pre_inst_reach_state             false
% 2.05/1.03  --bmc1_out_unsat_core                   false
% 2.05/1.03  --bmc1_aig_witness_out                  false
% 2.05/1.03  --bmc1_verbose                          false
% 2.05/1.03  --bmc1_dump_clauses_tptp                false
% 2.05/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.03  --bmc1_dump_file                        -
% 2.05/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.03  --bmc1_ucm_extend_mode                  1
% 2.05/1.03  --bmc1_ucm_init_mode                    2
% 2.05/1.03  --bmc1_ucm_cone_mode                    none
% 2.05/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.03  --bmc1_ucm_relax_model                  4
% 2.05/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.03  --bmc1_ucm_layered_model                none
% 2.05/1.03  --bmc1_ucm_max_lemma_size               10
% 2.05/1.03  
% 2.05/1.03  ------ AIG Options
% 2.05/1.03  
% 2.05/1.03  --aig_mode                              false
% 2.05/1.03  
% 2.05/1.03  ------ Instantiation Options
% 2.05/1.03  
% 2.05/1.03  --instantiation_flag                    true
% 2.05/1.03  --inst_sos_flag                         false
% 2.05/1.03  --inst_sos_phase                        true
% 2.05/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.03  --inst_lit_sel_side                     none
% 2.05/1.03  --inst_solver_per_active                1400
% 2.05/1.03  --inst_solver_calls_frac                1.
% 2.05/1.03  --inst_passive_queue_type               priority_queues
% 2.05/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.03  --inst_passive_queues_freq              [25;2]
% 2.05/1.03  --inst_dismatching                      true
% 2.05/1.03  --inst_eager_unprocessed_to_passive     true
% 2.05/1.03  --inst_prop_sim_given                   true
% 2.05/1.03  --inst_prop_sim_new                     false
% 2.05/1.03  --inst_subs_new                         false
% 2.05/1.03  --inst_eq_res_simp                      false
% 2.05/1.03  --inst_subs_given                       false
% 2.05/1.03  --inst_orphan_elimination               true
% 2.05/1.03  --inst_learning_loop_flag               true
% 2.05/1.03  --inst_learning_start                   3000
% 2.05/1.03  --inst_learning_factor                  2
% 2.05/1.03  --inst_start_prop_sim_after_learn       3
% 2.05/1.03  --inst_sel_renew                        solver
% 2.05/1.03  --inst_lit_activity_flag                true
% 2.05/1.03  --inst_restr_to_given                   false
% 2.05/1.03  --inst_activity_threshold               500
% 2.05/1.03  --inst_out_proof                        true
% 2.05/1.03  
% 2.05/1.03  ------ Resolution Options
% 2.05/1.03  
% 2.05/1.03  --resolution_flag                       false
% 2.05/1.03  --res_lit_sel                           adaptive
% 2.05/1.03  --res_lit_sel_side                      none
% 2.05/1.03  --res_ordering                          kbo
% 2.05/1.03  --res_to_prop_solver                    active
% 2.05/1.03  --res_prop_simpl_new                    false
% 2.05/1.03  --res_prop_simpl_given                  true
% 2.05/1.03  --res_passive_queue_type                priority_queues
% 2.05/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.03  --res_passive_queues_freq               [15;5]
% 2.05/1.03  --res_forward_subs                      full
% 2.05/1.03  --res_backward_subs                     full
% 2.05/1.03  --res_forward_subs_resolution           true
% 2.05/1.03  --res_backward_subs_resolution          true
% 2.05/1.03  --res_orphan_elimination                true
% 2.05/1.03  --res_time_limit                        2.
% 2.05/1.03  --res_out_proof                         true
% 2.05/1.03  
% 2.05/1.03  ------ Superposition Options
% 2.05/1.03  
% 2.05/1.03  --superposition_flag                    true
% 2.05/1.03  --sup_passive_queue_type                priority_queues
% 2.05/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.03  --demod_completeness_check              fast
% 2.05/1.03  --demod_use_ground                      true
% 2.05/1.03  --sup_to_prop_solver                    passive
% 2.05/1.03  --sup_prop_simpl_new                    true
% 2.05/1.03  --sup_prop_simpl_given                  true
% 2.05/1.03  --sup_fun_splitting                     false
% 2.05/1.03  --sup_smt_interval                      50000
% 2.05/1.03  
% 2.05/1.03  ------ Superposition Simplification Setup
% 2.05/1.03  
% 2.05/1.03  --sup_indices_passive                   []
% 2.05/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_full_bw                           [BwDemod]
% 2.05/1.03  --sup_immed_triv                        [TrivRules]
% 2.05/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_immed_bw_main                     []
% 2.05/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.03  
% 2.05/1.03  ------ Combination Options
% 2.05/1.03  
% 2.05/1.03  --comb_res_mult                         3
% 2.05/1.03  --comb_sup_mult                         2
% 2.05/1.03  --comb_inst_mult                        10
% 2.05/1.03  
% 2.05/1.03  ------ Debug Options
% 2.05/1.03  
% 2.05/1.03  --dbg_backtrace                         false
% 2.05/1.03  --dbg_dump_prop_clauses                 false
% 2.05/1.03  --dbg_dump_prop_clauses_file            -
% 2.05/1.03  --dbg_out_stat                          false
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  ------ Proving...
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  % SZS status Theorem for theBenchmark.p
% 2.05/1.03  
% 2.05/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/1.03  
% 2.05/1.03  fof(f1,axiom,(
% 2.05/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f42,plain,(
% 2.05/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f1])).
% 2.05/1.03  
% 2.05/1.03  fof(f14,conjecture,(
% 2.05/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f15,negated_conjecture,(
% 2.05/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.05/1.03    inference(negated_conjecture,[],[f14])).
% 2.05/1.03  
% 2.05/1.03  fof(f32,plain,(
% 2.05/1.03    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.05/1.03    inference(ennf_transformation,[],[f15])).
% 2.05/1.03  
% 2.05/1.03  fof(f33,plain,(
% 2.05/1.03    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.05/1.03    inference(flattening,[],[f32])).
% 2.05/1.03  
% 2.05/1.03  fof(f40,plain,(
% 2.05/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.05/1.03    introduced(choice_axiom,[])).
% 2.05/1.03  
% 2.05/1.03  fof(f39,plain,(
% 2.05/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.05/1.03    introduced(choice_axiom,[])).
% 2.05/1.03  
% 2.05/1.03  fof(f38,plain,(
% 2.05/1.03    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.05/1.03    introduced(choice_axiom,[])).
% 2.05/1.03  
% 2.05/1.03  fof(f37,plain,(
% 2.05/1.03    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.05/1.03    introduced(choice_axiom,[])).
% 2.05/1.03  
% 2.05/1.03  fof(f36,plain,(
% 2.05/1.03    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.05/1.03    introduced(choice_axiom,[])).
% 2.05/1.03  
% 2.05/1.03  fof(f41,plain,(
% 2.05/1.03    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.05/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f40,f39,f38,f37,f36])).
% 2.05/1.03  
% 2.05/1.03  fof(f67,plain,(
% 2.05/1.03    m1_subset_1(sK5,sK1)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f66,plain,(
% 2.05/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f64,plain,(
% 2.05/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f11,axiom,(
% 2.05/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f26,plain,(
% 2.05/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.05/1.03    inference(ennf_transformation,[],[f11])).
% 2.05/1.03  
% 2.05/1.03  fof(f27,plain,(
% 2.05/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.05/1.03    inference(flattening,[],[f26])).
% 2.05/1.03  
% 2.05/1.03  fof(f57,plain,(
% 2.05/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f27])).
% 2.05/1.03  
% 2.05/1.03  fof(f12,axiom,(
% 2.05/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f28,plain,(
% 2.05/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.05/1.03    inference(ennf_transformation,[],[f12])).
% 2.05/1.03  
% 2.05/1.03  fof(f29,plain,(
% 2.05/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.05/1.03    inference(flattening,[],[f28])).
% 2.05/1.03  
% 2.05/1.03  fof(f58,plain,(
% 2.05/1.03    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f29])).
% 2.05/1.03  
% 2.05/1.03  fof(f55,plain,(
% 2.05/1.03    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f27])).
% 2.05/1.03  
% 2.05/1.03  fof(f56,plain,(
% 2.05/1.03    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f27])).
% 2.05/1.03  
% 2.05/1.03  fof(f61,plain,(
% 2.05/1.03    ~v1_xboole_0(sK1)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f62,plain,(
% 2.05/1.03    v1_funct_1(sK3)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f63,plain,(
% 2.05/1.03    v1_funct_2(sK3,sK1,sK0)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f65,plain,(
% 2.05/1.03    v1_funct_1(sK4)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f69,plain,(
% 2.05/1.03    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f3,axiom,(
% 2.05/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f18,plain,(
% 2.05/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.05/1.03    inference(ennf_transformation,[],[f3])).
% 2.05/1.03  
% 2.05/1.03  fof(f44,plain,(
% 2.05/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f18])).
% 2.05/1.03  
% 2.05/1.03  fof(f5,axiom,(
% 2.05/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f47,plain,(
% 2.05/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.05/1.03    inference(cnf_transformation,[],[f5])).
% 2.05/1.03  
% 2.05/1.03  fof(f7,axiom,(
% 2.05/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f21,plain,(
% 2.05/1.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/1.03    inference(ennf_transformation,[],[f7])).
% 2.05/1.03  
% 2.05/1.03  fof(f49,plain,(
% 2.05/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/1.03    inference(cnf_transformation,[],[f21])).
% 2.05/1.03  
% 2.05/1.03  fof(f10,axiom,(
% 2.05/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f24,plain,(
% 2.05/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.05/1.03    inference(ennf_transformation,[],[f10])).
% 2.05/1.03  
% 2.05/1.03  fof(f25,plain,(
% 2.05/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.05/1.03    inference(flattening,[],[f24])).
% 2.05/1.03  
% 2.05/1.03  fof(f35,plain,(
% 2.05/1.03    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.05/1.03    inference(nnf_transformation,[],[f25])).
% 2.05/1.03  
% 2.05/1.03  fof(f53,plain,(
% 2.05/1.03    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f35])).
% 2.05/1.03  
% 2.05/1.03  fof(f68,plain,(
% 2.05/1.03    v1_partfun1(sK4,sK0)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  fof(f8,axiom,(
% 2.05/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f22,plain,(
% 2.05/1.03    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/1.03    inference(ennf_transformation,[],[f8])).
% 2.05/1.03  
% 2.05/1.03  fof(f51,plain,(
% 2.05/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/1.03    inference(cnf_transformation,[],[f22])).
% 2.05/1.03  
% 2.05/1.03  fof(f13,axiom,(
% 2.05/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f30,plain,(
% 2.05/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.05/1.03    inference(ennf_transformation,[],[f13])).
% 2.05/1.03  
% 2.05/1.03  fof(f31,plain,(
% 2.05/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.05/1.03    inference(flattening,[],[f30])).
% 2.05/1.03  
% 2.05/1.03  fof(f59,plain,(
% 2.05/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f31])).
% 2.05/1.03  
% 2.05/1.03  fof(f50,plain,(
% 2.05/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/1.03    inference(cnf_transformation,[],[f21])).
% 2.05/1.03  
% 2.05/1.03  fof(f4,axiom,(
% 2.05/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f19,plain,(
% 2.05/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.05/1.03    inference(ennf_transformation,[],[f4])).
% 2.05/1.03  
% 2.05/1.03  fof(f34,plain,(
% 2.05/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.05/1.03    inference(nnf_transformation,[],[f19])).
% 2.05/1.03  
% 2.05/1.03  fof(f45,plain,(
% 2.05/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f34])).
% 2.05/1.03  
% 2.05/1.03  fof(f9,axiom,(
% 2.05/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f23,plain,(
% 2.05/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/1.03    inference(ennf_transformation,[],[f9])).
% 2.05/1.03  
% 2.05/1.03  fof(f52,plain,(
% 2.05/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/1.03    inference(cnf_transformation,[],[f23])).
% 2.05/1.03  
% 2.05/1.03  fof(f2,axiom,(
% 2.05/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f16,plain,(
% 2.05/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.05/1.03    inference(ennf_transformation,[],[f2])).
% 2.05/1.03  
% 2.05/1.03  fof(f17,plain,(
% 2.05/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.05/1.03    inference(flattening,[],[f16])).
% 2.05/1.03  
% 2.05/1.03  fof(f43,plain,(
% 2.05/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f17])).
% 2.05/1.03  
% 2.05/1.03  fof(f6,axiom,(
% 2.05/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.05/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/1.03  
% 2.05/1.03  fof(f20,plain,(
% 2.05/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.05/1.03    inference(ennf_transformation,[],[f6])).
% 2.05/1.03  
% 2.05/1.03  fof(f48,plain,(
% 2.05/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.05/1.03    inference(cnf_transformation,[],[f20])).
% 2.05/1.03  
% 2.05/1.03  fof(f60,plain,(
% 2.05/1.03    ~v1_xboole_0(sK0)),
% 2.05/1.03    inference(cnf_transformation,[],[f41])).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1117,plain,
% 2.05/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.05/1.03      theory(equality) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1790,plain,
% 2.05/1.03      ( r1_tarski(X0,X1)
% 2.05/1.03      | ~ r1_tarski(k1_xboole_0,X2)
% 2.05/1.03      | X1 != X2
% 2.05/1.03      | X0 != k1_xboole_0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5760,plain,
% 2.05/1.03      ( r1_tarski(sK1,X0)
% 2.05/1.03      | ~ r1_tarski(k1_xboole_0,X1)
% 2.05/1.03      | X0 != X1
% 2.05/1.03      | sK1 != k1_xboole_0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1790]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_7370,plain,
% 2.05/1.03      ( r1_tarski(sK1,sK5)
% 2.05/1.03      | ~ r1_tarski(k1_xboole_0,X0)
% 2.05/1.03      | sK5 != X0
% 2.05/1.03      | sK1 != k1_xboole_0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_5760]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_9361,plain,
% 2.05/1.03      ( r1_tarski(sK1,sK5)
% 2.05/1.03      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.05/1.03      | sK5 != sK5
% 2.05/1.03      | sK1 != k1_xboole_0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_7370]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_0,plain,
% 2.05/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_6821,plain,
% 2.05/1.03      ( r1_tarski(k1_xboole_0,sK5) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_20,negated_conjecture,
% 2.05/1.03      ( m1_subset_1(sK5,sK1) ),
% 2.05/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1548,plain,
% 2.05/1.03      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_21,negated_conjecture,
% 2.05/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.05/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1547,plain,
% 2.05/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_23,negated_conjecture,
% 2.05/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.05/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1545,plain,
% 2.05/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_13,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 2.05/1.03      | ~ v1_funct_1(X3)
% 2.05/1.03      | ~ v1_funct_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1553,plain,
% 2.05/1.03      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.05/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.05/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 2.05/1.03      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 2.05/1.03      | v1_funct_1(X0) != iProver_top
% 2.05/1.03      | v1_funct_1(X3) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_16,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | ~ m1_subset_1(X3,X1)
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ v1_funct_1(X0)
% 2.05/1.03      | v1_xboole_0(X1)
% 2.05/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.05/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1550,plain,
% 2.05/1.03      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 2.05/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.05/1.03      | m1_subset_1(X3,X0) != iProver_top
% 2.05/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.05/1.03      | v1_funct_1(X2) != iProver_top
% 2.05/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2885,plain,
% 2.05/1.03      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 2.05/1.03      | v1_funct_2(X3,X0,X2) != iProver_top
% 2.05/1.03      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 2.05/1.03      | m1_subset_1(X5,X0) != iProver_top
% 2.05/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 2.05/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.05/1.03      | v1_funct_1(X3) != iProver_top
% 2.05/1.03      | v1_funct_1(X4) != iProver_top
% 2.05/1.03      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 2.05/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1553,c_1550]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_15,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ v1_funct_1(X3)
% 2.05/1.03      | ~ v1_funct_1(X0)
% 2.05/1.03      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 2.05/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1551,plain,
% 2.05/1.03      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.05/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.05/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 2.05/1.03      | v1_funct_1(X0) != iProver_top
% 2.05/1.03      | v1_funct_1(X3) != iProver_top
% 2.05/1.03      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_14,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 2.05/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ v1_funct_1(X4)
% 2.05/1.03      | ~ v1_funct_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1552,plain,
% 2.05/1.03      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.05/1.03      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 2.05/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.05/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.05/1.03      | v1_funct_1(X4) != iProver_top
% 2.05/1.03      | v1_funct_1(X0) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5416,plain,
% 2.05/1.03      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 2.05/1.03      | v1_funct_2(X3,X0,X2) != iProver_top
% 2.05/1.03      | m1_subset_1(X5,X0) != iProver_top
% 2.05/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 2.05/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.05/1.03      | v1_funct_1(X4) != iProver_top
% 2.05/1.03      | v1_funct_1(X3) != iProver_top
% 2.05/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.05/1.03      inference(forward_subsumption_resolution,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_2885,c_1551,c_1552]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5422,plain,
% 2.05/1.03      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 2.05/1.03      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.05/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.05/1.03      | m1_subset_1(X2,sK1) != iProver_top
% 2.05/1.03      | v1_funct_1(X1) != iProver_top
% 2.05/1.03      | v1_funct_1(sK3) != iProver_top
% 2.05/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1545,c_5416]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_26,negated_conjecture,
% 2.05/1.03      ( ~ v1_xboole_0(sK1) ),
% 2.05/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_29,plain,
% 2.05/1.03      ( v1_xboole_0(sK1) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_25,negated_conjecture,
% 2.05/1.03      ( v1_funct_1(sK3) ),
% 2.05/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_30,plain,
% 2.05/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_24,negated_conjecture,
% 2.05/1.03      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_31,plain,
% 2.05/1.03      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5584,plain,
% 2.05/1.03      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 2.05/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.05/1.03      | m1_subset_1(X2,sK1) != iProver_top
% 2.05/1.03      | v1_funct_1(X1) != iProver_top ),
% 2.05/1.03      inference(global_propositional_subsumption,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_5422,c_29,c_30,c_31]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5595,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 2.05/1.03      | m1_subset_1(X0,sK1) != iProver_top
% 2.05/1.03      | v1_funct_1(sK4) != iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1547,c_5584]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_22,negated_conjecture,
% 2.05/1.03      ( v1_funct_1(sK4) ),
% 2.05/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_33,plain,
% 2.05/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5717,plain,
% 2.05/1.03      ( m1_subset_1(X0,sK1) != iProver_top
% 2.05/1.03      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 2.05/1.03      inference(global_propositional_subsumption,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_5595,c_33]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5718,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 2.05/1.03      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.05/1.03      inference(renaming,[status(thm)],[c_5717]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5725,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1548,c_5718]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2352,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 2.05/1.03      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.05/1.03      | m1_subset_1(X0,sK1) != iProver_top
% 2.05/1.03      | v1_funct_1(sK3) != iProver_top
% 2.05/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1545,c_1550]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2595,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 2.05/1.03      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.05/1.03      inference(global_propositional_subsumption,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_2352,c_29,c_30,c_31]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2603,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1548,c_2595]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_18,negated_conjecture,
% 2.05/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.05/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2745,plain,
% 2.05/1.03      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.05/1.03      inference(demodulation,[status(thm)],[c_2603,c_18]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5727,plain,
% 2.05/1.03      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.05/1.03      inference(demodulation,[status(thm)],[c_5725,c_2745]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1116,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2486,plain,
% 2.05/1.03      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1116]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3027,plain,
% 2.05/1.03      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_2486]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_4912,plain,
% 2.05/1.03      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_3027]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2754,plain,
% 2.05/1.03      ( r1_tarski(X0,X1)
% 2.05/1.03      | ~ r1_tarski(k2_relat_1(sK3),X2)
% 2.05/1.03      | X1 != X2
% 2.05/1.03      | X0 != k2_relat_1(sK3) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3420,plain,
% 2.05/1.03      ( r1_tarski(k2_relset_1(sK1,sK0,sK3),X0)
% 2.05/1.03      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 2.05/1.03      | X0 != X1
% 2.05/1.03      | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_2754]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3779,plain,
% 2.05/1.03      ( r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
% 2.05/1.03      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.05/1.03      | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.05/1.03      | k1_relset_1(sK0,sK2,sK4) != X0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_3420]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3780,plain,
% 2.05/1.03      ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.05/1.03      | k1_relset_1(sK0,sK2,sK4) != X0
% 2.05/1.03      | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
% 2.05/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_3779]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3782,plain,
% 2.05/1.03      ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.05/1.03      | k1_relset_1(sK0,sK2,sK4) != sK0
% 2.05/1.03      | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
% 2.05/1.03      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_3780]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/1.03      | ~ v1_relat_1(X1)
% 2.05/1.03      | v1_relat_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1557,plain,
% 2.05/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.05/1.03      | v1_relat_1(X1) != iProver_top
% 2.05/1.03      | v1_relat_1(X0) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2332,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.05/1.03      | v1_relat_1(sK4) = iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1547,c_1557]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_34,plain,
% 2.05/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1738,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | v1_relat_1(X0)
% 2.05/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1934,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.05/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 2.05/1.03      | v1_relat_1(sK4) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1738]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1935,plain,
% 2.05/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.05/1.03      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.05/1.03      | v1_relat_1(sK4) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_5,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.05/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2117,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2118,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2525,plain,
% 2.05/1.03      ( v1_relat_1(sK4) = iProver_top ),
% 2.05/1.03      inference(global_propositional_subsumption,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_2332,c_34,c_1935,c_2118]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_8,plain,
% 2.05/1.03      ( v4_relat_1(X0,X1)
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.05/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_12,plain,
% 2.05/1.03      ( ~ v1_partfun1(X0,X1)
% 2.05/1.03      | ~ v4_relat_1(X0,X1)
% 2.05/1.03      | ~ v1_relat_1(X0)
% 2.05/1.03      | k1_relat_1(X0) = X1 ),
% 2.05/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_19,negated_conjecture,
% 2.05/1.03      ( v1_partfun1(sK4,sK0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_377,plain,
% 2.05/1.03      ( ~ v4_relat_1(X0,X1)
% 2.05/1.03      | ~ v1_relat_1(X0)
% 2.05/1.03      | k1_relat_1(X0) = X1
% 2.05/1.03      | sK4 != X0
% 2.05/1.03      | sK0 != X1 ),
% 2.05/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_378,plain,
% 2.05/1.03      ( ~ v4_relat_1(sK4,sK0)
% 2.05/1.03      | ~ v1_relat_1(sK4)
% 2.05/1.03      | k1_relat_1(sK4) = sK0 ),
% 2.05/1.03      inference(unflattening,[status(thm)],[c_377]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_394,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ v1_relat_1(sK4)
% 2.05/1.03      | k1_relat_1(sK4) = sK0
% 2.05/1.03      | sK4 != X0
% 2.05/1.03      | sK0 != X1 ),
% 2.05/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_378]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_395,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.05/1.03      | ~ v1_relat_1(sK4)
% 2.05/1.03      | k1_relat_1(sK4) = sK0 ),
% 2.05/1.03      inference(unflattening,[status(thm)],[c_394]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1113,plain,
% 2.05/1.03      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 2.05/1.03      inference(splitting,
% 2.05/1.03                [splitting(split),new_symbols(definition,[])],
% 2.05/1.03                [c_395]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1537,plain,
% 2.05/1.03      ( k1_relat_1(sK4) = sK0
% 2.05/1.03      | v1_relat_1(sK4) != iProver_top
% 2.05/1.03      | sP0_iProver_split = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2530,plain,
% 2.05/1.03      ( k1_relat_1(sK4) = sK0 | sP0_iProver_split = iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_2525,c_1537]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1143,plain,
% 2.05/1.03      ( k1_relat_1(sK4) = sK0
% 2.05/1.03      | v1_relat_1(sK4) != iProver_top
% 2.05/1.03      | sP0_iProver_split = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1112,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.05/1.03      | ~ sP0_iProver_split ),
% 2.05/1.03      inference(splitting,
% 2.05/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.05/1.03                [c_395]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1538,plain,
% 2.05/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.05/1.03      | sP0_iProver_split != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_1112]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2124,plain,
% 2.05/1.03      ( sP0_iProver_split != iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1547,c_1538]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3674,plain,
% 2.05/1.03      ( k1_relat_1(sK4) = sK0 ),
% 2.05/1.03      inference(global_propositional_subsumption,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_2530,c_34,c_1143,c_1935,c_2118,c_2124]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_9,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1555,plain,
% 2.05/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.05/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2138,plain,
% 2.05/1.03      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1547,c_1555]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_3677,plain,
% 2.05/1.03      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 2.05/1.03      inference(demodulation,[status(thm)],[c_3674,c_2138]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_17,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | ~ m1_subset_1(X3,X1)
% 2.05/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 2.05/1.03      | ~ v1_funct_1(X4)
% 2.05/1.03      | ~ v1_funct_1(X0)
% 2.05/1.03      | v1_xboole_0(X2)
% 2.05/1.03      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.05/1.03      | k1_xboole_0 = X1 ),
% 2.05/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1859,plain,
% 2.05/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.05/1.03      | ~ m1_subset_1(X3,X1)
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.05/1.03      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,sK4))
% 2.05/1.03      | ~ v1_funct_1(X0)
% 2.05/1.03      | ~ v1_funct_1(sK4)
% 2.05/1.03      | v1_xboole_0(X2)
% 2.05/1.03      | k1_funct_1(k8_funct_2(X1,X2,X4,X0,sK4),X3) = k1_funct_1(sK4,k1_funct_1(X0,X3))
% 2.05/1.03      | k1_xboole_0 = X1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2030,plain,
% 2.05/1.03      ( ~ v1_funct_2(sK3,X0,X1)
% 2.05/1.03      | ~ m1_subset_1(X2,X0)
% 2.05/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.05/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.05/1.03      | ~ r1_tarski(k2_relset_1(X0,X1,sK3),k1_relset_1(X1,X3,sK4))
% 2.05/1.03      | ~ v1_funct_1(sK4)
% 2.05/1.03      | ~ v1_funct_1(sK3)
% 2.05/1.03      | v1_xboole_0(X1)
% 2.05/1.03      | k1_funct_1(k8_funct_2(X0,X1,X3,sK3,sK4),X2) = k1_funct_1(sK4,k1_funct_1(sK3,X2))
% 2.05/1.03      | k1_xboole_0 = X0 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1859]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2191,plain,
% 2.05/1.03      ( ~ v1_funct_2(sK3,sK1,X0)
% 2.05/1.03      | ~ m1_subset_1(sK5,sK1)
% 2.05/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.05/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 2.05/1.03      | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relset_1(X0,X1,sK4))
% 2.05/1.03      | ~ v1_funct_1(sK4)
% 2.05/1.03      | ~ v1_funct_1(sK3)
% 2.05/1.03      | v1_xboole_0(X0)
% 2.05/1.03      | k1_funct_1(k8_funct_2(sK1,X0,X1,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.05/1.03      | k1_xboole_0 = sK1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_2030]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2379,plain,
% 2.05/1.03      ( ~ v1_funct_2(sK3,sK1,sK0)
% 2.05/1.03      | ~ m1_subset_1(sK5,sK1)
% 2.05/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.05/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.05/1.03      | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
% 2.05/1.03      | ~ v1_funct_1(sK4)
% 2.05/1.03      | ~ v1_funct_1(sK3)
% 2.05/1.03      | v1_xboole_0(sK0)
% 2.05/1.03      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.05/1.03      | k1_xboole_0 = sK1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_2191]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2380,plain,
% 2.05/1.03      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.05/1.03      | k1_xboole_0 = sK1
% 2.05/1.03      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.05/1.03      | m1_subset_1(sK5,sK1) != iProver_top
% 2.05/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.05/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.05/1.03      | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) != iProver_top
% 2.05/1.03      | v1_funct_1(sK4) != iProver_top
% 2.05/1.03      | v1_funct_1(sK3) != iProver_top
% 2.05/1.03      | v1_xboole_0(sK0) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_2379]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_7,plain,
% 2.05/1.03      ( v5_relat_1(X0,X1)
% 2.05/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.05/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_4,plain,
% 2.05/1.03      ( ~ v5_relat_1(X0,X1)
% 2.05/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 2.05/1.03      | ~ v1_relat_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_317,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 2.05/1.03      | ~ v1_relat_1(X0) ),
% 2.05/1.03      inference(resolution,[status(thm)],[c_7,c_4]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1539,plain,
% 2.05/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.05/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.05/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2262,plain,
% 2.05/1.03      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 2.05/1.03      | v1_relat_1(sK3) != iProver_top ),
% 2.05/1.03      inference(superposition,[status(thm)],[c_1545,c_1539]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1115,plain,( X0 = X0 ),theory(equality) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2237,plain,
% 2.05/1.03      ( sK1 = sK1 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2126,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_2127,plain,
% 2.05/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_2126]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1937,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.05/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.05/1.03      | v1_relat_1(sK3) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1738]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1938,plain,
% 2.05/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.05/1.03      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.05/1.03      | v1_relat_1(sK3) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1886,plain,
% 2.05/1.03      ( sK5 = sK5 ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_10,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.05/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1787,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.05/1.03      | k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.05/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_6,plain,
% 2.05/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_299,plain,
% 2.05/1.03      ( ~ m1_subset_1(X0,X1) | ~ r1_tarski(X1,X0) | v1_xboole_0(X1) ),
% 2.05/1.03      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_1758,plain,
% 2.05/1.03      ( ~ m1_subset_1(sK5,sK1)
% 2.05/1.03      | ~ r1_tarski(sK1,sK5)
% 2.05/1.03      | v1_xboole_0(sK1) ),
% 2.05/1.03      inference(instantiation,[status(thm)],[c_299]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_35,plain,
% 2.05/1.03      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_32,plain,
% 2.05/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_27,negated_conjecture,
% 2.05/1.03      ( ~ v1_xboole_0(sK0) ),
% 2.05/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(c_28,plain,
% 2.05/1.03      ( v1_xboole_0(sK0) != iProver_top ),
% 2.05/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.05/1.03  
% 2.05/1.03  cnf(contradiction,plain,
% 2.05/1.03      ( $false ),
% 2.05/1.03      inference(minisat,
% 2.05/1.03                [status(thm)],
% 2.05/1.03                [c_9361,c_6821,c_5727,c_4912,c_3782,c_3677,c_2380,c_2262,
% 2.05/1.03                 c_2237,c_2127,c_1938,c_1886,c_1787,c_1758,c_35,c_20,
% 2.05/1.03                 c_34,c_33,c_32,c_23,c_31,c_30,c_26,c_28]) ).
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/1.03  
% 2.05/1.03  ------                               Statistics
% 2.05/1.03  
% 2.05/1.03  ------ General
% 2.05/1.03  
% 2.05/1.03  abstr_ref_over_cycles:                  0
% 2.05/1.03  abstr_ref_under_cycles:                 0
% 2.05/1.03  gc_basic_clause_elim:                   0
% 2.05/1.03  forced_gc_time:                         0
% 2.05/1.03  parsing_time:                           0.012
% 2.05/1.03  unif_index_cands_time:                  0.
% 2.05/1.03  unif_index_add_time:                    0.
% 2.05/1.03  orderings_time:                         0.
% 2.05/1.03  out_proof_time:                         0.011
% 2.05/1.03  total_time:                             0.332
% 2.05/1.03  num_of_symbols:                         58
% 2.05/1.03  num_of_terms:                           11177
% 2.05/1.03  
% 2.05/1.03  ------ Preprocessing
% 2.05/1.03  
% 2.05/1.03  num_of_splits:                          1
% 2.05/1.03  num_of_split_atoms:                     1
% 2.05/1.03  num_of_reused_defs:                     0
% 2.05/1.03  num_eq_ax_congr_red:                    27
% 2.05/1.03  num_of_sem_filtered_clauses:            1
% 2.05/1.03  num_of_subtypes:                        1
% 2.05/1.03  monotx_restored_types:                  0
% 2.05/1.03  sat_num_of_epr_types:                   0
% 2.05/1.03  sat_num_of_non_cyclic_types:            0
% 2.05/1.03  sat_guarded_non_collapsed_types:        1
% 2.05/1.03  num_pure_diseq_elim:                    0
% 2.05/1.03  simp_replaced_by:                       0
% 2.05/1.03  res_preprocessed:                       125
% 2.05/1.03  prep_upred:                             0
% 2.05/1.03  prep_unflattend:                        32
% 2.05/1.03  smt_new_axioms:                         0
% 2.05/1.03  pred_elim_cands:                        6
% 2.05/1.03  pred_elim:                              4
% 2.05/1.03  pred_elim_cl:                           6
% 2.05/1.03  pred_elim_cycles:                       9
% 2.05/1.03  merged_defs:                            0
% 2.05/1.03  merged_defs_ncl:                        0
% 2.05/1.03  bin_hyper_res:                          0
% 2.05/1.03  prep_cycles:                            4
% 2.05/1.03  pred_elim_time:                         0.01
% 2.05/1.03  splitting_time:                         0.
% 2.05/1.03  sem_filter_time:                        0.
% 2.05/1.03  monotx_time:                            0.
% 2.05/1.03  subtype_inf_time:                       0.
% 2.05/1.03  
% 2.05/1.03  ------ Problem properties
% 2.05/1.03  
% 2.05/1.03  clauses:                                23
% 2.05/1.03  conjectures:                            9
% 2.05/1.03  epr:                                    8
% 2.05/1.03  horn:                                   20
% 2.05/1.03  ground:                                 10
% 2.05/1.03  unary:                                  11
% 2.05/1.03  binary:                                 3
% 2.05/1.03  lits:                                   63
% 2.05/1.03  lits_eq:                                7
% 2.05/1.03  fd_pure:                                0
% 2.05/1.03  fd_pseudo:                              0
% 2.05/1.03  fd_cond:                                1
% 2.05/1.03  fd_pseudo_cond:                         0
% 2.05/1.03  ac_symbols:                             0
% 2.05/1.03  
% 2.05/1.03  ------ Propositional Solver
% 2.05/1.03  
% 2.05/1.03  prop_solver_calls:                      33
% 2.05/1.03  prop_fast_solver_calls:                 2084
% 2.05/1.03  smt_solver_calls:                       0
% 2.05/1.03  smt_fast_solver_calls:                  0
% 2.05/1.03  prop_num_of_clauses:                    3368
% 2.05/1.03  prop_preprocess_simplified:             7286
% 2.05/1.03  prop_fo_subsumed:                       91
% 2.05/1.03  prop_solver_time:                       0.
% 2.05/1.03  smt_solver_time:                        0.
% 2.05/1.03  smt_fast_solver_time:                   0.
% 2.05/1.03  prop_fast_solver_time:                  0.
% 2.05/1.03  prop_unsat_core_time:                   0.
% 2.05/1.03  
% 2.05/1.03  ------ QBF
% 2.05/1.03  
% 2.05/1.03  qbf_q_res:                              0
% 2.05/1.03  qbf_num_tautologies:                    0
% 2.05/1.03  qbf_prep_cycles:                        0
% 2.05/1.03  
% 2.05/1.03  ------ BMC1
% 2.05/1.03  
% 2.05/1.03  bmc1_current_bound:                     -1
% 2.05/1.03  bmc1_last_solved_bound:                 -1
% 2.05/1.03  bmc1_unsat_core_size:                   -1
% 2.05/1.03  bmc1_unsat_core_parents_size:           -1
% 2.05/1.03  bmc1_merge_next_fun:                    0
% 2.05/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.05/1.03  
% 2.05/1.03  ------ Instantiation
% 2.05/1.03  
% 2.05/1.03  inst_num_of_clauses:                    864
% 2.05/1.03  inst_num_in_passive:                    156
% 2.05/1.03  inst_num_in_active:                     656
% 2.05/1.03  inst_num_in_unprocessed:                51
% 2.05/1.03  inst_num_of_loops:                      686
% 2.05/1.03  inst_num_of_learning_restarts:          0
% 2.05/1.03  inst_num_moves_active_passive:          22
% 2.05/1.03  inst_lit_activity:                      0
% 2.05/1.03  inst_lit_activity_moves:                0
% 2.05/1.03  inst_num_tautologies:                   0
% 2.05/1.03  inst_num_prop_implied:                  0
% 2.05/1.03  inst_num_existing_simplified:           0
% 2.05/1.03  inst_num_eq_res_simplified:             0
% 2.05/1.03  inst_num_child_elim:                    0
% 2.05/1.03  inst_num_of_dismatching_blockings:      216
% 2.05/1.03  inst_num_of_non_proper_insts:           925
% 2.05/1.03  inst_num_of_duplicates:                 0
% 2.05/1.03  inst_inst_num_from_inst_to_res:         0
% 2.05/1.03  inst_dismatching_checking_time:         0.
% 2.05/1.03  
% 2.05/1.03  ------ Resolution
% 2.05/1.03  
% 2.05/1.03  res_num_of_clauses:                     0
% 2.05/1.03  res_num_in_passive:                     0
% 2.05/1.03  res_num_in_active:                      0
% 2.05/1.03  res_num_of_loops:                       129
% 2.05/1.03  res_forward_subset_subsumed:            193
% 2.05/1.03  res_backward_subset_subsumed:           0
% 2.05/1.03  res_forward_subsumed:                   0
% 2.05/1.03  res_backward_subsumed:                  0
% 2.05/1.03  res_forward_subsumption_resolution:     0
% 2.05/1.03  res_backward_subsumption_resolution:    0
% 2.05/1.03  res_clause_to_clause_subsumption:       2017
% 2.05/1.03  res_orphan_elimination:                 0
% 2.05/1.03  res_tautology_del:                      131
% 2.05/1.03  res_num_eq_res_simplified:              0
% 2.05/1.03  res_num_sel_changes:                    0
% 2.05/1.03  res_moves_from_active_to_pass:          0
% 2.05/1.03  
% 2.05/1.03  ------ Superposition
% 2.05/1.03  
% 2.05/1.03  sup_time_total:                         0.
% 2.05/1.03  sup_time_generating:                    0.
% 2.05/1.03  sup_time_sim_full:                      0.
% 2.05/1.03  sup_time_sim_immed:                     0.
% 2.05/1.03  
% 2.05/1.03  sup_num_of_clauses:                     191
% 2.05/1.03  sup_num_in_active:                      132
% 2.05/1.03  sup_num_in_passive:                     59
% 2.05/1.03  sup_num_of_loops:                       136
% 2.05/1.03  sup_fw_superposition:                   158
% 2.05/1.03  sup_bw_superposition:                   12
% 2.05/1.03  sup_immediate_simplified:               1
% 2.05/1.03  sup_given_eliminated:                   0
% 2.05/1.03  comparisons_done:                       0
% 2.05/1.03  comparisons_avoided:                    10
% 2.05/1.03  
% 2.05/1.03  ------ Simplifications
% 2.05/1.03  
% 2.05/1.03  
% 2.05/1.03  sim_fw_subset_subsumed:                 0
% 2.05/1.03  sim_bw_subset_subsumed:                 1
% 2.05/1.03  sim_fw_subsumed:                        0
% 2.05/1.03  sim_bw_subsumed:                        0
% 2.05/1.03  sim_fw_subsumption_res:                 41
% 2.05/1.03  sim_bw_subsumption_res:                 0
% 2.05/1.03  sim_tautology_del:                      0
% 2.05/1.03  sim_eq_tautology_del:                   0
% 2.05/1.03  sim_eq_res_simp:                        0
% 2.05/1.03  sim_fw_demodulated:                     0
% 2.05/1.03  sim_bw_demodulated:                     3
% 2.05/1.03  sim_light_normalised:                   2
% 2.05/1.03  sim_joinable_taut:                      0
% 2.05/1.03  sim_joinable_simp:                      0
% 2.05/1.03  sim_ac_normalised:                      0
% 2.05/1.03  sim_smt_subsumption:                    0
% 2.05/1.03  
%------------------------------------------------------------------------------
