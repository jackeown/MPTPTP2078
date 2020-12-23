%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:19 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 581 expanded)
%              Number of clauses        :  119 ( 182 expanded)
%              Number of leaves         :   20 ( 200 expanded)
%              Depth                    :   19
%              Number of atoms          :  673 (4389 expanded)
%              Number of equality atoms :  248 ( 742 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f35,f34,f33,f32,f31])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
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

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_879,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1340,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1331,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_1788,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1340,c_1331])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_884,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ r1_tarski(k2_relset_1(X0_54,X1_54,X0_53),k1_relset_1(X1_54,X2_54,X1_53))
    | ~ m1_subset_1(X2_53,X0_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_xboole_0(X1_54)
    | k1_xboole_0 = X0_54
    | k1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X2_53) = k1_funct_1(X1_53,k1_funct_1(X0_53,X2_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1336,plain,
    ( k1_xboole_0 = X0_54
    | k1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X2_53) = k1_funct_1(X1_53,k1_funct_1(X0_53,X2_53))
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | r1_tarski(k2_relset_1(X0_54,X1_54,X0_53),k1_relset_1(X1_54,X2_54,X1_53)) != iProver_top
    | m1_subset_1(X2_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_2576,plain,
    ( sK1 = k1_xboole_0
    | k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(X0_53,k1_funct_1(sK3,X1_53))
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0_54,X0_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
    | m1_subset_1(X1_53,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1336])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_898,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1637,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_892,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_1687,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1688,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_891,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1746,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_1747,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1746])).

cnf(c_1611,plain,
    ( ~ v1_funct_2(X0_53,sK1,X0_54)
    | ~ r1_tarski(k2_relset_1(sK1,X0_54,X0_53),k1_relset_1(X0_54,X1_54,X1_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_54)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_xboole_0(X0_54)
    | k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,X0_54,X1_54,X0_53,X1_53),sK5) = k1_funct_1(X1_53,k1_funct_1(X0_53,sK5)) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1760,plain,
    ( ~ v1_funct_2(X0_53,sK1,sK0)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,X0_53),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_53,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_53,sK5)) ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_1761,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_53,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_53,sK5))
    | v1_funct_2(X0_53,sK1,sK0) != iProver_top
    | r1_tarski(k2_relset_1(sK1,sK0,X0_53),k1_relset_1(sK0,sK2,sK4)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_1763,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) != iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_334,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_335,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_335])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_873,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_895,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_873])).

cnf(c_1346,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_966,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1685,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_1743,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_1744,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_881,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1338,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_873])).

cnf(c_1347,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_1902,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1347])).

cnf(c_1942,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_32,c_966,c_1685,c_1744,c_1902])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k1_relset_1(X0_54,X1_54,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1330,plain,
    ( k1_relset_1(X0_54,X1_54,X0_53) = k1_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_1754,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1338,c_1330])).

cnf(c_1945,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_1942,c_1754])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_274,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_874,plain,
    ( r1_tarski(k2_relat_1(X0_53),X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_2226,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_2227,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_907,plain,
    ( ~ r1_tarski(X0_55,X0_54)
    | r1_tarski(X1_55,X1_54)
    | X1_55 != X0_55
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2558,plain,
    ( r1_tarski(X0_55,X0_54)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | X0_55 != k2_relat_1(sK3)
    | X0_54 != sK0 ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_3443,plain,
    ( r1_tarski(k2_relset_1(sK1,sK0,sK3),X0_54)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | X0_54 != sK0 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_3826,plain,
    ( r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK4) != sK0 ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_3828,plain,
    ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK4) != sK0
    | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3826])).

cnf(c_882,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1337,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_888,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1332,plain,
    ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_885,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X0_54)
    | k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1335,plain,
    ( k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_2132,plain,
    ( k3_funct_2(X0_54,X1_54,k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53) = k1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53)
    | v1_funct_2(X0_53,X0_54,X2_54) != iProver_top
    | v1_funct_2(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X0_54,X1_54) != iProver_top
    | m1_subset_1(X2_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_1335])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_886,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1334,plain,
    ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_887,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X0_54,X2_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1333,plain,
    ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X0_54,X2_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_3349,plain,
    ( k3_funct_2(X0_54,X1_54,k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53) = k1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53)
    | v1_funct_2(X0_53,X0_54,X2_54) != iProver_top
    | m1_subset_1(X2_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2132,c_1334,c_1333])).

cnf(c_3354,plain,
    ( k3_funct_2(sK1,X0_54,k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
    | m1_subset_1(X1_53,sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_3349])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3840,plain,
    ( k3_funct_2(sK1,X0_54,k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
    | m1_subset_1(X1_53,sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_27,c_28,c_29])).

cnf(c_3850,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53)
    | m1_subset_1(X0_53,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_3840])).

cnf(c_3881,plain,
    ( m1_subset_1(X0_53,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_31])).

cnf(c_3882,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53)
    | m1_subset_1(X0_53,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3881])).

cnf(c_3889,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1337,c_3882])).

cnf(c_2034,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_53) = k1_funct_1(sK3,X0_53)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0_53,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1335])).

cnf(c_2353,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_53) = k1_funct_1(sK3,X0_53)
    | m1_subset_1(X0_53,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2034,c_27,c_28,c_29])).

cnf(c_2361,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1337,c_2353])).

cnf(c_16,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_883,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2435,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2361,c_883])).

cnf(c_3949,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3889,c_2435])).

cnf(c_901,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1847,plain,
    ( X0_54 != X1_54
    | sK1 != X1_54
    | sK1 = X0_54 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_2076,plain,
    ( X0_54 != sK1
    | sK1 = X0_54
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_4711,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_4956,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_26,c_28,c_29,c_21,c_30,c_31,c_32,c_33,c_1563,c_1637,c_1688,c_1747,c_1763,c_1945,c_2227,c_3828,c_3949,c_4711])).

cnf(c_876,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1343,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_4986,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4956,c_1343])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_78,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4986,c_78])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:35:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.98  
% 2.52/0.98  ------  iProver source info
% 2.52/0.98  
% 2.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.98  git: non_committed_changes: false
% 2.52/0.98  git: last_make_outside_of_git: false
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options
% 2.52/0.98  
% 2.52/0.98  --out_options                           all
% 2.52/0.98  --tptp_safe_out                         true
% 2.52/0.98  --problem_path                          ""
% 2.52/0.98  --include_path                          ""
% 2.52/0.98  --clausifier                            res/vclausify_rel
% 2.52/0.98  --clausifier_options                    --mode clausify
% 2.52/0.98  --stdin                                 false
% 2.52/0.98  --stats_out                             all
% 2.52/0.98  
% 2.52/0.98  ------ General Options
% 2.52/0.98  
% 2.52/0.98  --fof                                   false
% 2.52/0.98  --time_out_real                         305.
% 2.52/0.98  --time_out_virtual                      -1.
% 2.52/0.98  --symbol_type_check                     false
% 2.52/0.98  --clausify_out                          false
% 2.52/0.98  --sig_cnt_out                           false
% 2.52/0.98  --trig_cnt_out                          false
% 2.52/0.98  --trig_cnt_out_tolerance                1.
% 2.52/0.98  --trig_cnt_out_sk_spl                   false
% 2.52/0.98  --abstr_cl_out                          false
% 2.52/0.98  
% 2.52/0.98  ------ Global Options
% 2.52/0.98  
% 2.52/0.98  --schedule                              default
% 2.52/0.98  --add_important_lit                     false
% 2.52/0.98  --prop_solver_per_cl                    1000
% 2.52/0.98  --min_unsat_core                        false
% 2.52/0.98  --soft_assumptions                      false
% 2.52/0.98  --soft_lemma_size                       3
% 2.52/0.98  --prop_impl_unit_size                   0
% 2.52/0.98  --prop_impl_unit                        []
% 2.52/0.98  --share_sel_clauses                     true
% 2.52/0.98  --reset_solvers                         false
% 2.52/0.98  --bc_imp_inh                            [conj_cone]
% 2.52/0.98  --conj_cone_tolerance                   3.
% 2.52/0.98  --extra_neg_conj                        none
% 2.52/0.98  --large_theory_mode                     true
% 2.52/0.98  --prolific_symb_bound                   200
% 2.52/0.98  --lt_threshold                          2000
% 2.52/0.98  --clause_weak_htbl                      true
% 2.52/0.98  --gc_record_bc_elim                     false
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing Options
% 2.52/0.98  
% 2.52/0.98  --preprocessing_flag                    true
% 2.52/0.98  --time_out_prep_mult                    0.1
% 2.52/0.98  --splitting_mode                        input
% 2.52/0.98  --splitting_grd                         true
% 2.52/0.98  --splitting_cvd                         false
% 2.52/0.98  --splitting_cvd_svl                     false
% 2.52/0.98  --splitting_nvd                         32
% 2.52/0.98  --sub_typing                            true
% 2.52/0.98  --prep_gs_sim                           true
% 2.52/0.98  --prep_unflatten                        true
% 2.52/0.98  --prep_res_sim                          true
% 2.52/0.98  --prep_upred                            true
% 2.52/0.98  --prep_sem_filter                       exhaustive
% 2.52/0.98  --prep_sem_filter_out                   false
% 2.52/0.98  --pred_elim                             true
% 2.52/0.98  --res_sim_input                         true
% 2.52/0.98  --eq_ax_congr_red                       true
% 2.52/0.98  --pure_diseq_elim                       true
% 2.52/0.98  --brand_transform                       false
% 2.52/0.98  --non_eq_to_eq                          false
% 2.52/0.98  --prep_def_merge                        true
% 2.52/0.98  --prep_def_merge_prop_impl              false
% 2.52/0.98  --prep_def_merge_mbd                    true
% 2.52/0.98  --prep_def_merge_tr_red                 false
% 2.52/0.98  --prep_def_merge_tr_cl                  false
% 2.52/0.98  --smt_preprocessing                     true
% 2.52/0.98  --smt_ac_axioms                         fast
% 2.52/0.98  --preprocessed_out                      false
% 2.52/0.98  --preprocessed_stats                    false
% 2.52/0.98  
% 2.52/0.98  ------ Abstraction refinement Options
% 2.52/0.98  
% 2.52/0.98  --abstr_ref                             []
% 2.52/0.98  --abstr_ref_prep                        false
% 2.52/0.98  --abstr_ref_until_sat                   false
% 2.52/0.98  --abstr_ref_sig_restrict                funpre
% 2.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.98  --abstr_ref_under                       []
% 2.52/0.98  
% 2.52/0.98  ------ SAT Options
% 2.52/0.98  
% 2.52/0.98  --sat_mode                              false
% 2.52/0.98  --sat_fm_restart_options                ""
% 2.52/0.98  --sat_gr_def                            false
% 2.52/0.98  --sat_epr_types                         true
% 2.52/0.98  --sat_non_cyclic_types                  false
% 2.52/0.98  --sat_finite_models                     false
% 2.52/0.98  --sat_fm_lemmas                         false
% 2.52/0.98  --sat_fm_prep                           false
% 2.52/0.98  --sat_fm_uc_incr                        true
% 2.52/0.98  --sat_out_model                         small
% 2.52/0.98  --sat_out_clauses                       false
% 2.52/0.98  
% 2.52/0.98  ------ QBF Options
% 2.52/0.98  
% 2.52/0.98  --qbf_mode                              false
% 2.52/0.98  --qbf_elim_univ                         false
% 2.52/0.98  --qbf_dom_inst                          none
% 2.52/0.98  --qbf_dom_pre_inst                      false
% 2.52/0.98  --qbf_sk_in                             false
% 2.52/0.98  --qbf_pred_elim                         true
% 2.52/0.98  --qbf_split                             512
% 2.52/0.98  
% 2.52/0.98  ------ BMC1 Options
% 2.52/0.98  
% 2.52/0.98  --bmc1_incremental                      false
% 2.52/0.98  --bmc1_axioms                           reachable_all
% 2.52/0.98  --bmc1_min_bound                        0
% 2.52/0.98  --bmc1_max_bound                        -1
% 2.52/0.98  --bmc1_max_bound_default                -1
% 2.52/0.98  --bmc1_symbol_reachability              true
% 2.52/0.98  --bmc1_property_lemmas                  false
% 2.52/0.98  --bmc1_k_induction                      false
% 2.52/0.98  --bmc1_non_equiv_states                 false
% 2.52/0.98  --bmc1_deadlock                         false
% 2.52/0.98  --bmc1_ucm                              false
% 2.52/0.98  --bmc1_add_unsat_core                   none
% 2.52/0.98  --bmc1_unsat_core_children              false
% 2.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.98  --bmc1_out_stat                         full
% 2.52/0.98  --bmc1_ground_init                      false
% 2.52/0.98  --bmc1_pre_inst_next_state              false
% 2.52/0.98  --bmc1_pre_inst_state                   false
% 2.52/0.98  --bmc1_pre_inst_reach_state             false
% 2.52/0.98  --bmc1_out_unsat_core                   false
% 2.52/0.98  --bmc1_aig_witness_out                  false
% 2.52/0.98  --bmc1_verbose                          false
% 2.52/0.98  --bmc1_dump_clauses_tptp                false
% 2.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.98  --bmc1_dump_file                        -
% 2.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.98  --bmc1_ucm_extend_mode                  1
% 2.52/0.98  --bmc1_ucm_init_mode                    2
% 2.52/0.98  --bmc1_ucm_cone_mode                    none
% 2.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.98  --bmc1_ucm_relax_model                  4
% 2.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.98  --bmc1_ucm_layered_model                none
% 2.52/0.98  --bmc1_ucm_max_lemma_size               10
% 2.52/0.98  
% 2.52/0.98  ------ AIG Options
% 2.52/0.98  
% 2.52/0.98  --aig_mode                              false
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation Options
% 2.52/0.98  
% 2.52/0.98  --instantiation_flag                    true
% 2.52/0.98  --inst_sos_flag                         false
% 2.52/0.98  --inst_sos_phase                        true
% 2.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel_side                     num_symb
% 2.52/0.98  --inst_solver_per_active                1400
% 2.52/0.98  --inst_solver_calls_frac                1.
% 2.52/0.98  --inst_passive_queue_type               priority_queues
% 2.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.98  --inst_passive_queues_freq              [25;2]
% 2.52/0.98  --inst_dismatching                      true
% 2.52/0.98  --inst_eager_unprocessed_to_passive     true
% 2.52/0.98  --inst_prop_sim_given                   true
% 2.52/0.98  --inst_prop_sim_new                     false
% 2.52/0.98  --inst_subs_new                         false
% 2.52/0.98  --inst_eq_res_simp                      false
% 2.52/0.98  --inst_subs_given                       false
% 2.52/0.98  --inst_orphan_elimination               true
% 2.52/0.98  --inst_learning_loop_flag               true
% 2.52/0.98  --inst_learning_start                   3000
% 2.52/0.98  --inst_learning_factor                  2
% 2.52/0.98  --inst_start_prop_sim_after_learn       3
% 2.52/0.98  --inst_sel_renew                        solver
% 2.52/0.98  --inst_lit_activity_flag                true
% 2.52/0.98  --inst_restr_to_given                   false
% 2.52/0.98  --inst_activity_threshold               500
% 2.52/0.98  --inst_out_proof                        true
% 2.52/0.98  
% 2.52/0.98  ------ Resolution Options
% 2.52/0.98  
% 2.52/0.98  --resolution_flag                       true
% 2.52/0.98  --res_lit_sel                           adaptive
% 2.52/0.98  --res_lit_sel_side                      none
% 2.52/0.98  --res_ordering                          kbo
% 2.52/0.98  --res_to_prop_solver                    active
% 2.52/0.98  --res_prop_simpl_new                    false
% 2.52/0.98  --res_prop_simpl_given                  true
% 2.52/0.98  --res_passive_queue_type                priority_queues
% 2.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.98  --res_passive_queues_freq               [15;5]
% 2.52/0.98  --res_forward_subs                      full
% 2.52/0.98  --res_backward_subs                     full
% 2.52/0.98  --res_forward_subs_resolution           true
% 2.52/0.98  --res_backward_subs_resolution          true
% 2.52/0.98  --res_orphan_elimination                true
% 2.52/0.98  --res_time_limit                        2.
% 2.52/0.98  --res_out_proof                         true
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Options
% 2.52/0.98  
% 2.52/0.98  --superposition_flag                    true
% 2.52/0.98  --sup_passive_queue_type                priority_queues
% 2.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.98  --demod_completeness_check              fast
% 2.52/0.98  --demod_use_ground                      true
% 2.52/0.98  --sup_to_prop_solver                    passive
% 2.52/0.98  --sup_prop_simpl_new                    true
% 2.52/0.98  --sup_prop_simpl_given                  true
% 2.52/0.98  --sup_fun_splitting                     false
% 2.52/0.98  --sup_smt_interval                      50000
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Simplification Setup
% 2.52/0.98  
% 2.52/0.98  --sup_indices_passive                   []
% 2.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_full_bw                           [BwDemod]
% 2.52/0.98  --sup_immed_triv                        [TrivRules]
% 2.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_immed_bw_main                     []
% 2.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  
% 2.52/0.98  ------ Combination Options
% 2.52/0.98  
% 2.52/0.98  --comb_res_mult                         3
% 2.52/0.98  --comb_sup_mult                         2
% 2.52/0.98  --comb_inst_mult                        10
% 2.52/0.98  
% 2.52/0.98  ------ Debug Options
% 2.52/0.98  
% 2.52/0.98  --dbg_backtrace                         false
% 2.52/0.98  --dbg_dump_prop_clauses                 false
% 2.52/0.98  --dbg_dump_prop_clauses_file            -
% 2.52/0.98  --dbg_out_stat                          false
% 2.52/0.98  ------ Parsing...
% 2.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.98  ------ Proving...
% 2.52/0.98  ------ Problem Properties 
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  clauses                                 22
% 2.52/0.98  conjectures                             9
% 2.52/0.98  EPR                                     7
% 2.52/0.98  Horn                                    19
% 2.52/0.98  unary                                   11
% 2.52/0.98  binary                                  3
% 2.52/0.98  lits                                    60
% 2.52/0.98  lits eq                                 7
% 2.52/0.98  fd_pure                                 0
% 2.52/0.98  fd_pseudo                               0
% 2.52/0.98  fd_cond                                 1
% 2.52/0.98  fd_pseudo_cond                          0
% 2.52/0.98  AC symbols                              0
% 2.52/0.98  
% 2.52/0.98  ------ Schedule dynamic 5 is on 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  Current options:
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options
% 2.52/0.98  
% 2.52/0.98  --out_options                           all
% 2.52/0.98  --tptp_safe_out                         true
% 2.52/0.98  --problem_path                          ""
% 2.52/0.98  --include_path                          ""
% 2.52/0.98  --clausifier                            res/vclausify_rel
% 2.52/0.98  --clausifier_options                    --mode clausify
% 2.52/0.98  --stdin                                 false
% 2.52/0.98  --stats_out                             all
% 2.52/0.98  
% 2.52/0.98  ------ General Options
% 2.52/0.98  
% 2.52/0.98  --fof                                   false
% 2.52/0.98  --time_out_real                         305.
% 2.52/0.98  --time_out_virtual                      -1.
% 2.52/0.98  --symbol_type_check                     false
% 2.52/0.98  --clausify_out                          false
% 2.52/0.98  --sig_cnt_out                           false
% 2.52/0.98  --trig_cnt_out                          false
% 2.52/0.98  --trig_cnt_out_tolerance                1.
% 2.52/0.98  --trig_cnt_out_sk_spl                   false
% 2.52/0.98  --abstr_cl_out                          false
% 2.52/0.98  
% 2.52/0.98  ------ Global Options
% 2.52/0.98  
% 2.52/0.98  --schedule                              default
% 2.52/0.98  --add_important_lit                     false
% 2.52/0.98  --prop_solver_per_cl                    1000
% 2.52/0.98  --min_unsat_core                        false
% 2.52/0.98  --soft_assumptions                      false
% 2.52/0.98  --soft_lemma_size                       3
% 2.52/0.98  --prop_impl_unit_size                   0
% 2.52/0.98  --prop_impl_unit                        []
% 2.52/0.98  --share_sel_clauses                     true
% 2.52/0.98  --reset_solvers                         false
% 2.52/0.98  --bc_imp_inh                            [conj_cone]
% 2.52/0.98  --conj_cone_tolerance                   3.
% 2.52/0.98  --extra_neg_conj                        none
% 2.52/0.98  --large_theory_mode                     true
% 2.52/0.98  --prolific_symb_bound                   200
% 2.52/0.98  --lt_threshold                          2000
% 2.52/0.98  --clause_weak_htbl                      true
% 2.52/0.98  --gc_record_bc_elim                     false
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing Options
% 2.52/0.98  
% 2.52/0.98  --preprocessing_flag                    true
% 2.52/0.98  --time_out_prep_mult                    0.1
% 2.52/0.98  --splitting_mode                        input
% 2.52/0.98  --splitting_grd                         true
% 2.52/0.98  --splitting_cvd                         false
% 2.52/0.98  --splitting_cvd_svl                     false
% 2.52/0.98  --splitting_nvd                         32
% 2.52/0.98  --sub_typing                            true
% 2.52/0.98  --prep_gs_sim                           true
% 2.52/0.98  --prep_unflatten                        true
% 2.52/0.98  --prep_res_sim                          true
% 2.52/0.98  --prep_upred                            true
% 2.52/0.98  --prep_sem_filter                       exhaustive
% 2.52/0.98  --prep_sem_filter_out                   false
% 2.52/0.98  --pred_elim                             true
% 2.52/0.98  --res_sim_input                         true
% 2.52/0.98  --eq_ax_congr_red                       true
% 2.52/0.98  --pure_diseq_elim                       true
% 2.52/0.98  --brand_transform                       false
% 2.52/0.98  --non_eq_to_eq                          false
% 2.52/0.98  --prep_def_merge                        true
% 2.52/0.98  --prep_def_merge_prop_impl              false
% 2.52/0.98  --prep_def_merge_mbd                    true
% 2.52/0.98  --prep_def_merge_tr_red                 false
% 2.52/0.98  --prep_def_merge_tr_cl                  false
% 2.52/0.98  --smt_preprocessing                     true
% 2.52/0.98  --smt_ac_axioms                         fast
% 2.52/0.98  --preprocessed_out                      false
% 2.52/0.98  --preprocessed_stats                    false
% 2.52/0.98  
% 2.52/0.98  ------ Abstraction refinement Options
% 2.52/0.98  
% 2.52/0.98  --abstr_ref                             []
% 2.52/0.98  --abstr_ref_prep                        false
% 2.52/0.98  --abstr_ref_until_sat                   false
% 2.52/0.98  --abstr_ref_sig_restrict                funpre
% 2.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.98  --abstr_ref_under                       []
% 2.52/0.98  
% 2.52/0.98  ------ SAT Options
% 2.52/0.98  
% 2.52/0.98  --sat_mode                              false
% 2.52/0.98  --sat_fm_restart_options                ""
% 2.52/0.98  --sat_gr_def                            false
% 2.52/0.98  --sat_epr_types                         true
% 2.52/0.98  --sat_non_cyclic_types                  false
% 2.52/0.98  --sat_finite_models                     false
% 2.52/0.98  --sat_fm_lemmas                         false
% 2.52/0.98  --sat_fm_prep                           false
% 2.52/0.98  --sat_fm_uc_incr                        true
% 2.52/0.98  --sat_out_model                         small
% 2.52/0.98  --sat_out_clauses                       false
% 2.52/0.98  
% 2.52/0.98  ------ QBF Options
% 2.52/0.98  
% 2.52/0.98  --qbf_mode                              false
% 2.52/0.98  --qbf_elim_univ                         false
% 2.52/0.98  --qbf_dom_inst                          none
% 2.52/0.98  --qbf_dom_pre_inst                      false
% 2.52/0.98  --qbf_sk_in                             false
% 2.52/0.98  --qbf_pred_elim                         true
% 2.52/0.98  --qbf_split                             512
% 2.52/0.98  
% 2.52/0.98  ------ BMC1 Options
% 2.52/0.98  
% 2.52/0.98  --bmc1_incremental                      false
% 2.52/0.98  --bmc1_axioms                           reachable_all
% 2.52/0.98  --bmc1_min_bound                        0
% 2.52/0.98  --bmc1_max_bound                        -1
% 2.52/0.98  --bmc1_max_bound_default                -1
% 2.52/0.98  --bmc1_symbol_reachability              true
% 2.52/0.98  --bmc1_property_lemmas                  false
% 2.52/0.98  --bmc1_k_induction                      false
% 2.52/0.98  --bmc1_non_equiv_states                 false
% 2.52/0.98  --bmc1_deadlock                         false
% 2.52/0.98  --bmc1_ucm                              false
% 2.52/0.98  --bmc1_add_unsat_core                   none
% 2.52/0.98  --bmc1_unsat_core_children              false
% 2.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.98  --bmc1_out_stat                         full
% 2.52/0.98  --bmc1_ground_init                      false
% 2.52/0.98  --bmc1_pre_inst_next_state              false
% 2.52/0.98  --bmc1_pre_inst_state                   false
% 2.52/0.98  --bmc1_pre_inst_reach_state             false
% 2.52/0.98  --bmc1_out_unsat_core                   false
% 2.52/0.98  --bmc1_aig_witness_out                  false
% 2.52/0.98  --bmc1_verbose                          false
% 2.52/0.98  --bmc1_dump_clauses_tptp                false
% 2.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.98  --bmc1_dump_file                        -
% 2.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.98  --bmc1_ucm_extend_mode                  1
% 2.52/0.98  --bmc1_ucm_init_mode                    2
% 2.52/0.98  --bmc1_ucm_cone_mode                    none
% 2.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.98  --bmc1_ucm_relax_model                  4
% 2.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.98  --bmc1_ucm_layered_model                none
% 2.52/0.98  --bmc1_ucm_max_lemma_size               10
% 2.52/0.98  
% 2.52/0.98  ------ AIG Options
% 2.52/0.98  
% 2.52/0.98  --aig_mode                              false
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation Options
% 2.52/0.98  
% 2.52/0.98  --instantiation_flag                    true
% 2.52/0.98  --inst_sos_flag                         false
% 2.52/0.98  --inst_sos_phase                        true
% 2.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel_side                     none
% 2.52/0.98  --inst_solver_per_active                1400
% 2.52/0.98  --inst_solver_calls_frac                1.
% 2.52/0.98  --inst_passive_queue_type               priority_queues
% 2.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.98  --inst_passive_queues_freq              [25;2]
% 2.52/0.98  --inst_dismatching                      true
% 2.52/0.98  --inst_eager_unprocessed_to_passive     true
% 2.52/0.98  --inst_prop_sim_given                   true
% 2.52/0.98  --inst_prop_sim_new                     false
% 2.52/0.98  --inst_subs_new                         false
% 2.52/0.98  --inst_eq_res_simp                      false
% 2.52/0.98  --inst_subs_given                       false
% 2.52/0.98  --inst_orphan_elimination               true
% 2.52/0.98  --inst_learning_loop_flag               true
% 2.52/0.98  --inst_learning_start                   3000
% 2.52/0.98  --inst_learning_factor                  2
% 2.52/0.98  --inst_start_prop_sim_after_learn       3
% 2.52/0.98  --inst_sel_renew                        solver
% 2.52/0.98  --inst_lit_activity_flag                true
% 2.52/0.98  --inst_restr_to_given                   false
% 2.52/0.98  --inst_activity_threshold               500
% 2.52/0.98  --inst_out_proof                        true
% 2.52/0.98  
% 2.52/0.98  ------ Resolution Options
% 2.52/0.98  
% 2.52/0.98  --resolution_flag                       false
% 2.52/0.98  --res_lit_sel                           adaptive
% 2.52/0.98  --res_lit_sel_side                      none
% 2.52/0.98  --res_ordering                          kbo
% 2.52/0.98  --res_to_prop_solver                    active
% 2.52/0.98  --res_prop_simpl_new                    false
% 2.52/0.98  --res_prop_simpl_given                  true
% 2.52/0.98  --res_passive_queue_type                priority_queues
% 2.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.98  --res_passive_queues_freq               [15;5]
% 2.52/0.98  --res_forward_subs                      full
% 2.52/0.98  --res_backward_subs                     full
% 2.52/0.98  --res_forward_subs_resolution           true
% 2.52/0.98  --res_backward_subs_resolution          true
% 2.52/0.98  --res_orphan_elimination                true
% 2.52/0.98  --res_time_limit                        2.
% 2.52/0.98  --res_out_proof                         true
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Options
% 2.52/0.98  
% 2.52/0.98  --superposition_flag                    true
% 2.52/0.98  --sup_passive_queue_type                priority_queues
% 2.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.98  --demod_completeness_check              fast
% 2.52/0.98  --demod_use_ground                      true
% 2.52/0.98  --sup_to_prop_solver                    passive
% 2.52/0.98  --sup_prop_simpl_new                    true
% 2.52/0.98  --sup_prop_simpl_given                  true
% 2.52/0.98  --sup_fun_splitting                     false
% 2.52/0.98  --sup_smt_interval                      50000
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Simplification Setup
% 2.52/0.98  
% 2.52/0.98  --sup_indices_passive                   []
% 2.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_full_bw                           [BwDemod]
% 2.52/0.98  --sup_immed_triv                        [TrivRules]
% 2.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_immed_bw_main                     []
% 2.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  
% 2.52/0.98  ------ Combination Options
% 2.52/0.98  
% 2.52/0.98  --comb_res_mult                         3
% 2.52/0.98  --comb_sup_mult                         2
% 2.52/0.98  --comb_inst_mult                        10
% 2.52/0.98  
% 2.52/0.98  ------ Debug Options
% 2.52/0.98  
% 2.52/0.98  --dbg_backtrace                         false
% 2.52/0.98  --dbg_dump_prop_clauses                 false
% 2.52/0.98  --dbg_dump_prop_clauses_file            -
% 2.52/0.98  --dbg_out_stat                          false
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  ------ Proving...
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  % SZS status Theorem for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  fof(f12,conjecture,(
% 2.52/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f13,negated_conjecture,(
% 2.52/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.52/0.98    inference(negated_conjecture,[],[f12])).
% 2.52/0.98  
% 2.52/0.98  fof(f27,plain,(
% 2.52/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.52/0.98    inference(ennf_transformation,[],[f13])).
% 2.52/0.98  
% 2.52/0.98  fof(f28,plain,(
% 2.52/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.52/0.98    inference(flattening,[],[f27])).
% 2.52/0.98  
% 2.52/0.98  fof(f35,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f34,plain,(
% 2.52/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f33,plain,(
% 2.52/0.98    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f32,plain,(
% 2.52/0.98    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f31,plain,(
% 2.52/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f36,plain,(
% 2.52/0.98    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f35,f34,f33,f32,f31])).
% 2.52/0.98  
% 2.52/0.98  fof(f57,plain,(
% 2.52/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f7,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f18,plain,(
% 2.52/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.98    inference(ennf_transformation,[],[f7])).
% 2.52/0.98  
% 2.52/0.98  fof(f45,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f18])).
% 2.52/0.98  
% 2.52/0.98  fof(f11,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f25,plain,(
% 2.52/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.52/0.98    inference(ennf_transformation,[],[f11])).
% 2.52/0.98  
% 2.52/0.98  fof(f26,plain,(
% 2.52/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.52/0.98    inference(flattening,[],[f25])).
% 2.52/0.98  
% 2.52/0.98  fof(f52,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f26])).
% 2.52/0.98  
% 2.52/0.98  fof(f53,plain,(
% 2.52/0.98    ~v1_xboole_0(sK0)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f55,plain,(
% 2.52/0.98    v1_funct_1(sK3)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f56,plain,(
% 2.52/0.98    v1_funct_2(sK3,sK1,sK0)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f58,plain,(
% 2.52/0.98    v1_funct_1(sK4)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f59,plain,(
% 2.52/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f60,plain,(
% 2.52/0.98    m1_subset_1(sK5,sK1)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f2,axiom,(
% 2.52/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f14,plain,(
% 2.52/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.52/0.98    inference(ennf_transformation,[],[f2])).
% 2.52/0.98  
% 2.52/0.98  fof(f38,plain,(
% 2.52/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f14])).
% 2.52/0.98  
% 2.52/0.98  fof(f4,axiom,(
% 2.52/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f41,plain,(
% 2.52/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f4])).
% 2.52/0.98  
% 2.52/0.98  fof(f5,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f16,plain,(
% 2.52/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.98    inference(ennf_transformation,[],[f5])).
% 2.52/0.98  
% 2.52/0.98  fof(f42,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f16])).
% 2.52/0.98  
% 2.52/0.98  fof(f8,axiom,(
% 2.52/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f19,plain,(
% 2.52/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.52/0.98    inference(ennf_transformation,[],[f8])).
% 2.52/0.98  
% 2.52/0.98  fof(f20,plain,(
% 2.52/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.52/0.98    inference(flattening,[],[f19])).
% 2.52/0.98  
% 2.52/0.98  fof(f30,plain,(
% 2.52/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.52/0.98    inference(nnf_transformation,[],[f20])).
% 2.52/0.98  
% 2.52/0.98  fof(f46,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f30])).
% 2.52/0.98  
% 2.52/0.98  fof(f61,plain,(
% 2.52/0.98    v1_partfun1(sK4,sK0)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f6,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f17,plain,(
% 2.52/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.98    inference(ennf_transformation,[],[f6])).
% 2.52/0.98  
% 2.52/0.98  fof(f44,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f17])).
% 2.52/0.98  
% 2.52/0.98  fof(f43,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f16])).
% 2.52/0.98  
% 2.52/0.98  fof(f3,axiom,(
% 2.52/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f15,plain,(
% 2.52/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.52/0.98    inference(ennf_transformation,[],[f3])).
% 2.52/0.98  
% 2.52/0.98  fof(f29,plain,(
% 2.52/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.52/0.98    inference(nnf_transformation,[],[f15])).
% 2.52/0.98  
% 2.52/0.98  fof(f39,plain,(
% 2.52/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f29])).
% 2.52/0.98  
% 2.52/0.98  fof(f9,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f21,plain,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.52/0.98    inference(ennf_transformation,[],[f9])).
% 2.52/0.98  
% 2.52/0.98  fof(f22,plain,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.52/0.98    inference(flattening,[],[f21])).
% 2.52/0.98  
% 2.52/0.98  fof(f50,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f22])).
% 2.52/0.98  
% 2.52/0.98  fof(f10,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f23,plain,(
% 2.52/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.52/0.98    inference(ennf_transformation,[],[f10])).
% 2.52/0.98  
% 2.52/0.98  fof(f24,plain,(
% 2.52/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.52/0.98    inference(flattening,[],[f23])).
% 2.52/0.98  
% 2.52/0.98  fof(f51,plain,(
% 2.52/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f24])).
% 2.52/0.98  
% 2.52/0.98  fof(f48,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f22])).
% 2.52/0.98  
% 2.52/0.98  fof(f49,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f22])).
% 2.52/0.98  
% 2.52/0.98  fof(f54,plain,(
% 2.52/0.98    ~v1_xboole_0(sK1)),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f62,plain,(
% 2.52/0.98    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.52/0.98    inference(cnf_transformation,[],[f36])).
% 2.52/0.98  
% 2.52/0.98  fof(f1,axiom,(
% 2.52/0.98    v1_xboole_0(k1_xboole_0)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f37,plain,(
% 2.52/0.98    v1_xboole_0(k1_xboole_0)),
% 2.52/0.98    inference(cnf_transformation,[],[f1])).
% 2.52/0.98  
% 2.52/0.98  cnf(c_21,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.52/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_879,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1340,plain,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_8,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_889,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1331,plain,
% 2.52/0.98      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1788,plain,
% 2.52/0.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1340,c_1331]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_15,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.52/0.98      | ~ m1_subset_1(X5,X1)
% 2.52/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | ~ v1_funct_1(X4)
% 2.52/0.98      | ~ v1_funct_1(X0)
% 2.52/0.98      | v1_xboole_0(X2)
% 2.52/0.98      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.52/0.98      | k1_xboole_0 = X1 ),
% 2.52/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_884,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.52/0.98      | ~ r1_tarski(k2_relset_1(X0_54,X1_54,X0_53),k1_relset_1(X1_54,X2_54,X1_53))
% 2.52/0.98      | ~ m1_subset_1(X2_53,X0_54)
% 2.52/0.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(X1_53)
% 2.52/0.98      | v1_xboole_0(X1_54)
% 2.52/0.98      | k1_xboole_0 = X0_54
% 2.52/0.98      | k1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X2_53) = k1_funct_1(X1_53,k1_funct_1(X0_53,X2_53)) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1336,plain,
% 2.52/0.98      ( k1_xboole_0 = X0_54
% 2.52/0.98      | k1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X2_53) = k1_funct_1(X1_53,k1_funct_1(X0_53,X2_53))
% 2.52/0.98      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.52/0.98      | r1_tarski(k2_relset_1(X0_54,X1_54,X0_53),k1_relset_1(X1_54,X2_54,X1_53)) != iProver_top
% 2.52/0.98      | m1_subset_1(X2_53,X0_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top
% 2.52/0.98      | v1_xboole_0(X1_54) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_884]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2576,plain,
% 2.52/0.98      ( sK1 = k1_xboole_0
% 2.52/0.98      | k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(X0_53,k1_funct_1(sK3,X1_53))
% 2.52/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.52/0.98      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0_54,X0_53)) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,sK1) != iProver_top
% 2.52/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(sK3) != iProver_top
% 2.52/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1788,c_1336]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_25,negated_conjecture,
% 2.52/0.98      ( ~ v1_xboole_0(sK0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_26,plain,
% 2.52/0.98      ( v1_xboole_0(sK0) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_23,negated_conjecture,
% 2.52/0.98      ( v1_funct_1(sK3) ),
% 2.52/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_28,plain,
% 2.52/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_22,negated_conjecture,
% 2.52/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_29,plain,
% 2.52/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_30,plain,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_20,negated_conjecture,
% 2.52/0.98      ( v1_funct_1(sK4) ),
% 2.52/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_31,plain,
% 2.52/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_19,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.52/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_32,plain,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_18,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.52/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_33,plain,
% 2.52/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1563,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.52/0.98      | k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_889]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_898,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1637,plain,
% 2.52/0.98      ( sK1 = sK1 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_898]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.98      | ~ v1_relat_1(X1)
% 2.52/0.98      | v1_relat_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_892,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.52/0.98      | ~ v1_relat_1(X1_53)
% 2.52/0.98      | v1_relat_1(X0_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1519,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | v1_relat_1(X0_53)
% 2.52/0.98      | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_892]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1687,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.52/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.52/0.98      | v1_relat_1(sK3) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_1519]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1688,plain,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.52/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.52/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_4,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.52/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_891,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1746,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_891]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1747,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1746]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1611,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,sK1,X0_54)
% 2.52/0.98      | ~ r1_tarski(k2_relset_1(sK1,X0_54,X0_53),k1_relset_1(X0_54,X1_54,X1_53))
% 2.52/0.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_54)))
% 2.52/0.98      | ~ m1_subset_1(sK5,sK1)
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(X1_53)
% 2.52/0.98      | v1_xboole_0(X0_54)
% 2.52/0.98      | k1_xboole_0 = sK1
% 2.52/0.98      | k1_funct_1(k8_funct_2(sK1,X0_54,X1_54,X0_53,X1_53),sK5) = k1_funct_1(X1_53,k1_funct_1(X0_53,sK5)) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_884]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1760,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,sK1,sK0)
% 2.52/0.98      | ~ r1_tarski(k2_relset_1(sK1,sK0,X0_53),k1_relset_1(sK0,sK2,sK4))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.52/0.98      | ~ m1_subset_1(sK5,sK1)
% 2.52/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(sK4)
% 2.52/0.98      | v1_xboole_0(sK0)
% 2.52/0.98      | k1_xboole_0 = sK1
% 2.52/0.98      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_53,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_53,sK5)) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_1611]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1761,plain,
% 2.52/0.98      ( k1_xboole_0 = sK1
% 2.52/0.98      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_53,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_53,sK5))
% 2.52/0.98      | v1_funct_2(X0_53,sK1,sK0) != iProver_top
% 2.52/0.98      | r1_tarski(k2_relset_1(sK1,sK0,X0_53),k1_relset_1(sK0,sK2,sK4)) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.52/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.52/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(sK4) != iProver_top
% 2.52/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1763,plain,
% 2.52/0.98      ( k1_xboole_0 = sK1
% 2.52/0.98      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.52/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.52/0.98      | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) != iProver_top
% 2.52/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.52/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.52/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.52/0.98      | v1_funct_1(sK4) != iProver_top
% 2.52/0.98      | v1_funct_1(sK3) != iProver_top
% 2.52/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_6,plain,
% 2.52/0.98      ( v4_relat_1(X0,X1)
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.52/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_10,plain,
% 2.52/0.98      ( ~ v1_partfun1(X0,X1)
% 2.52/0.98      | ~ v4_relat_1(X0,X1)
% 2.52/0.98      | ~ v1_relat_1(X0)
% 2.52/0.98      | k1_relat_1(X0) = X1 ),
% 2.52/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_17,negated_conjecture,
% 2.52/0.98      ( v1_partfun1(sK4,sK0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_334,plain,
% 2.52/0.98      ( ~ v4_relat_1(X0,X1)
% 2.52/0.98      | ~ v1_relat_1(X0)
% 2.52/0.98      | k1_relat_1(X0) = X1
% 2.52/0.98      | sK4 != X0
% 2.52/0.98      | sK0 != X1 ),
% 2.52/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_335,plain,
% 2.52/0.98      ( ~ v4_relat_1(sK4,sK0)
% 2.52/0.98      | ~ v1_relat_1(sK4)
% 2.52/0.98      | k1_relat_1(sK4) = sK0 ),
% 2.52/0.98      inference(unflattening,[status(thm)],[c_334]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_351,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | ~ v1_relat_1(sK4)
% 2.52/0.98      | k1_relat_1(sK4) = sK0
% 2.52/0.98      | sK4 != X0
% 2.52/0.98      | sK0 != X1 ),
% 2.52/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_335]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_352,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.52/0.98      | ~ v1_relat_1(sK4)
% 2.52/0.98      | k1_relat_1(sK4) = sK0 ),
% 2.52/0.98      inference(unflattening,[status(thm)],[c_351]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_873,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54)))
% 2.52/0.98      | ~ v1_relat_1(sK4)
% 2.52/0.98      | k1_relat_1(sK4) = sK0 ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_352]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_895,plain,
% 2.52/0.98      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 2.52/0.98      inference(splitting,
% 2.52/0.98                [splitting(split),new_symbols(definition,[])],
% 2.52/0.98                [c_873]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1346,plain,
% 2.52/0.98      ( k1_relat_1(sK4) = sK0
% 2.52/0.98      | v1_relat_1(sK4) != iProver_top
% 2.52/0.98      | sP0_iProver_split = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_895]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_966,plain,
% 2.52/0.98      ( k1_relat_1(sK4) = sK0
% 2.52/0.98      | v1_relat_1(sK4) != iProver_top
% 2.52/0.98      | sP0_iProver_split = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_895]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1684,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.52/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 2.52/0.98      | v1_relat_1(sK4) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_1519]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1685,plain,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.52/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.52/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1743,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_891]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1744,plain,
% 2.52/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_881,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1338,plain,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_881]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_894,plain,
% 2.52/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54)))
% 2.52/0.98      | ~ sP0_iProver_split ),
% 2.52/0.98      inference(splitting,
% 2.52/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.52/0.98                [c_873]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1347,plain,
% 2.52/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
% 2.52/0.98      | sP0_iProver_split != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1902,plain,
% 2.52/0.98      ( sP0_iProver_split != iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1338,c_1347]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1942,plain,
% 2.52/0.98      ( k1_relat_1(sK4) = sK0 ),
% 2.52/0.98      inference(global_propositional_subsumption,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_1346,c_32,c_966,c_1685,c_1744,c_1902]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_7,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_890,plain,
% 2.52/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | k1_relset_1(X0_54,X1_54,X0_53) = k1_relat_1(X0_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1330,plain,
% 2.52/0.98      ( k1_relset_1(X0_54,X1_54,X0_53) = k1_relat_1(X0_53)
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1754,plain,
% 2.52/0.98      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1338,c_1330]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1945,plain,
% 2.52/0.98      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 2.52/0.98      inference(demodulation,[status(thm)],[c_1942,c_1754]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_5,plain,
% 2.52/0.98      ( v5_relat_1(X0,X1)
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.52/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3,plain,
% 2.52/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.52/0.98      | ~ v5_relat_1(X0,X1)
% 2.52/0.98      | ~ v1_relat_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_274,plain,
% 2.52/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.52/0.98      | ~ v1_relat_1(X0) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_874,plain,
% 2.52/0.98      ( r1_tarski(k2_relat_1(X0_53),X0_54)
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.52/0.98      | ~ v1_relat_1(X0_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_274]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2226,plain,
% 2.52/0.98      ( r1_tarski(k2_relat_1(sK3),sK0)
% 2.52/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.52/0.98      | ~ v1_relat_1(sK3) ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_874]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2227,plain,
% 2.52/0.98      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 2.52/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.52/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_907,plain,
% 2.52/0.98      ( ~ r1_tarski(X0_55,X0_54)
% 2.52/0.98      | r1_tarski(X1_55,X1_54)
% 2.52/0.98      | X1_55 != X0_55
% 2.52/0.98      | X1_54 != X0_54 ),
% 2.52/0.98      theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2558,plain,
% 2.52/0.98      ( r1_tarski(X0_55,X0_54)
% 2.52/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK0)
% 2.52/0.98      | X0_55 != k2_relat_1(sK3)
% 2.52/0.98      | X0_54 != sK0 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_907]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3443,plain,
% 2.52/0.98      ( r1_tarski(k2_relset_1(sK1,sK0,sK3),X0_54)
% 2.52/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK0)
% 2.52/0.98      | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.52/0.98      | X0_54 != sK0 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_2558]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3826,plain,
% 2.52/0.98      ( r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
% 2.52/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK0)
% 2.52/0.98      | k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.52/0.98      | k1_relset_1(sK0,sK2,sK4) != sK0 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_3443]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3828,plain,
% 2.52/0.98      ( k2_relset_1(sK1,sK0,sK3) != k2_relat_1(sK3)
% 2.52/0.98      | k1_relset_1(sK0,sK2,sK4) != sK0
% 2.52/0.98      | r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) = iProver_top
% 2.52/0.98      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_3826]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_882,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1337,plain,
% 2.52/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_11,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 2.52/0.98      | ~ v1_funct_1(X3)
% 2.52/0.98      | ~ v1_funct_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_888,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.52/0.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | m1_subset_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(X1_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1332,plain,
% 2.52/0.98      ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) = iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_14,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.98      | ~ m1_subset_1(X3,X1)
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | ~ v1_funct_1(X0)
% 2.52/0.98      | v1_xboole_0(X1)
% 2.52/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.52/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_885,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.52/0.98      | ~ m1_subset_1(X1_53,X0_54)
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | v1_xboole_0(X0_54)
% 2.52/0.98      | k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1335,plain,
% 2.52/0.98      ( k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53)
% 2.52/0.98      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,X0_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_xboole_0(X0_54) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2132,plain,
% 2.52/0.98      ( k3_funct_2(X0_54,X1_54,k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53) = k1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53)
% 2.52/0.98      | v1_funct_2(X0_53,X0_54,X2_54) != iProver_top
% 2.52/0.98      | v1_funct_2(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X0_54,X1_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X2_53,X0_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top
% 2.52/0.98      | v1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53)) != iProver_top
% 2.52/0.98      | v1_xboole_0(X0_54) = iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1332,c_1335]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_13,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | ~ v1_funct_1(X3)
% 2.52/0.98      | ~ v1_funct_1(X0)
% 2.52/0.98      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 2.52/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_886,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.52/0.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(X1_53)
% 2.52/0.98      | v1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53)) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1334,plain,
% 2.52/0.98      ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top
% 2.52/0.98      | v1_funct_1(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53)) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_12,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.98      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 2.52/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.52/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.98      | ~ v1_funct_1(X4)
% 2.52/0.98      | ~ v1_funct_1(X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_887,plain,
% 2.52/0.98      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.52/0.98      | v1_funct_2(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X0_54,X2_54)
% 2.52/0.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.52/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.52/0.98      | ~ v1_funct_1(X0_53)
% 2.52/0.98      | ~ v1_funct_1(X1_53) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1333,plain,
% 2.52/0.98      ( v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.52/0.98      | v1_funct_2(k8_funct_2(X0_54,X1_54,X2_54,X0_53,X1_53),X0_54,X2_54) = iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_887]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3349,plain,
% 2.52/0.98      ( k3_funct_2(X0_54,X1_54,k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53) = k1_funct_1(k8_funct_2(X0_54,X2_54,X1_54,X0_53,X1_53),X2_53)
% 2.52/0.98      | v1_funct_2(X0_53,X0_54,X2_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X2_53,X0_54) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X2_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(X1_53) != iProver_top
% 2.52/0.98      | v1_xboole_0(X0_54) = iProver_top ),
% 2.52/0.98      inference(forward_subsumption_resolution,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_2132,c_1334,c_1333]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3354,plain,
% 2.52/0.98      ( k3_funct_2(sK1,X0_54,k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53)
% 2.52/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,sK1) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top
% 2.52/0.98      | v1_funct_1(sK3) != iProver_top
% 2.52/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1340,c_3349]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_24,negated_conjecture,
% 2.52/0.98      ( ~ v1_xboole_0(sK1) ),
% 2.52/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_27,plain,
% 2.52/0.98      ( v1_xboole_0(sK1) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3840,plain,
% 2.52/0.98      ( k3_funct_2(sK1,X0_54,k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53) = k1_funct_1(k8_funct_2(sK1,sK0,X0_54,sK3,X0_53),X1_53)
% 2.52/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_54))) != iProver_top
% 2.52/0.98      | m1_subset_1(X1_53,sK1) != iProver_top
% 2.52/0.98      | v1_funct_1(X0_53) != iProver_top ),
% 2.52/0.98      inference(global_propositional_subsumption,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_3354,c_27,c_28,c_29]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3850,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53)
% 2.52/0.98      | m1_subset_1(X0_53,sK1) != iProver_top
% 2.52/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1338,c_3840]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3881,plain,
% 2.52/0.98      ( m1_subset_1(X0_53,sK1) != iProver_top
% 2.52/0.98      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) ),
% 2.52/0.98      inference(global_propositional_subsumption,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_3850,c_31]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3882,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_53)
% 2.52/0.98      | m1_subset_1(X0_53,sK1) != iProver_top ),
% 2.52/0.98      inference(renaming,[status(thm)],[c_3881]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3889,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1337,c_3882]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2034,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK0,sK3,X0_53) = k1_funct_1(sK3,X0_53)
% 2.52/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.52/0.98      | m1_subset_1(X0_53,sK1) != iProver_top
% 2.52/0.98      | v1_funct_1(sK3) != iProver_top
% 2.52/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1340,c_1335]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2353,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK0,sK3,X0_53) = k1_funct_1(sK3,X0_53)
% 2.52/0.98      | m1_subset_1(X0_53,sK1) != iProver_top ),
% 2.52/0.98      inference(global_propositional_subsumption,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_2034,c_27,c_28,c_29]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2361,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.52/0.98      inference(superposition,[status(thm)],[c_1337,c_2353]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_16,negated_conjecture,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.52/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_883,negated_conjecture,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2435,plain,
% 2.52/0.98      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.52/0.98      inference(demodulation,[status(thm)],[c_2361,c_883]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3949,plain,
% 2.52/0.98      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.52/0.98      inference(demodulation,[status(thm)],[c_3889,c_2435]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_901,plain,
% 2.52/0.98      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.52/0.98      theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1847,plain,
% 2.52/0.98      ( X0_54 != X1_54 | sK1 != X1_54 | sK1 = X0_54 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_901]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2076,plain,
% 2.52/0.98      ( X0_54 != sK1 | sK1 = X0_54 | sK1 != sK1 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_1847]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_4711,plain,
% 2.52/0.98      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.52/0.98      inference(instantiation,[status(thm)],[c_2076]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_4956,plain,
% 2.52/0.98      ( sK1 = k1_xboole_0 ),
% 2.52/0.98      inference(global_propositional_subsumption,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_2576,c_26,c_28,c_29,c_21,c_30,c_31,c_32,c_33,c_1563,
% 2.52/0.98                 c_1637,c_1688,c_1747,c_1763,c_1945,c_2227,c_3828,c_3949,
% 2.52/0.98                 c_4711]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_876,negated_conjecture,
% 2.52/0.98      ( ~ v1_xboole_0(sK1) ),
% 2.52/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1343,plain,
% 2.52/0.98      ( v1_xboole_0(sK1) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_4986,plain,
% 2.52/0.98      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.52/0.98      inference(demodulation,[status(thm)],[c_4956,c_1343]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_0,plain,
% 2.52/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_78,plain,
% 2.52/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(contradiction,plain,
% 2.52/0.98      ( $false ),
% 2.52/0.98      inference(minisat,[status(thm)],[c_4986,c_78]) ).
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  ------                               Statistics
% 2.52/0.98  
% 2.52/0.98  ------ General
% 2.52/0.98  
% 2.52/0.98  abstr_ref_over_cycles:                  0
% 2.52/0.98  abstr_ref_under_cycles:                 0
% 2.52/0.98  gc_basic_clause_elim:                   0
% 2.52/0.98  forced_gc_time:                         0
% 2.52/0.98  parsing_time:                           0.009
% 2.52/0.98  unif_index_cands_time:                  0.
% 2.52/0.98  unif_index_add_time:                    0.
% 2.52/0.98  orderings_time:                         0.
% 2.52/0.98  out_proof_time:                         0.011
% 2.52/0.98  total_time:                             0.206
% 2.52/0.98  num_of_symbols:                         60
% 2.52/0.98  num_of_terms:                           4902
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing
% 2.52/0.98  
% 2.52/0.98  num_of_splits:                          1
% 2.52/0.98  num_of_split_atoms:                     1
% 2.52/0.98  num_of_reused_defs:                     0
% 2.52/0.98  num_eq_ax_congr_red:                    25
% 2.52/0.98  num_of_sem_filtered_clauses:            1
% 2.52/0.98  num_of_subtypes:                        3
% 2.52/0.98  monotx_restored_types:                  0
% 2.52/0.98  sat_num_of_epr_types:                   0
% 2.52/0.98  sat_num_of_non_cyclic_types:            0
% 2.52/0.98  sat_guarded_non_collapsed_types:        1
% 2.52/0.98  num_pure_diseq_elim:                    0
% 2.52/0.98  simp_replaced_by:                       0
% 2.52/0.98  res_preprocessed:                       128
% 2.52/0.98  prep_upred:                             0
% 2.52/0.98  prep_unflattend:                        18
% 2.52/0.98  smt_new_axioms:                         0
% 2.52/0.98  pred_elim_cands:                        6
% 2.52/0.98  pred_elim:                              3
% 2.52/0.98  pred_elim_cl:                           5
% 2.52/0.98  pred_elim_cycles:                       8
% 2.52/0.98  merged_defs:                            0
% 2.52/0.98  merged_defs_ncl:                        0
% 2.52/0.98  bin_hyper_res:                          0
% 2.52/0.98  prep_cycles:                            4
% 2.52/0.98  pred_elim_time:                         0.026
% 2.52/0.98  splitting_time:                         0.
% 2.52/0.98  sem_filter_time:                        0.
% 2.52/0.98  monotx_time:                            0.
% 2.52/0.98  subtype_inf_time:                       0.
% 2.52/0.98  
% 2.52/0.98  ------ Problem properties
% 2.52/0.98  
% 2.52/0.98  clauses:                                22
% 2.52/0.98  conjectures:                            9
% 2.52/0.98  epr:                                    7
% 2.52/0.98  horn:                                   19
% 2.52/0.98  ground:                                 11
% 2.52/0.98  unary:                                  11
% 2.52/0.98  binary:                                 3
% 2.52/0.98  lits:                                   60
% 2.52/0.98  lits_eq:                                7
% 2.52/0.98  fd_pure:                                0
% 2.52/0.98  fd_pseudo:                              0
% 2.52/0.98  fd_cond:                                1
% 2.52/0.98  fd_pseudo_cond:                         0
% 2.52/0.98  ac_symbols:                             0
% 2.52/0.98  
% 2.52/0.98  ------ Propositional Solver
% 2.52/0.98  
% 2.52/0.98  prop_solver_calls:                      30
% 2.52/0.98  prop_fast_solver_calls:                 1311
% 2.52/0.98  smt_solver_calls:                       0
% 2.52/0.98  smt_fast_solver_calls:                  0
% 2.52/0.98  prop_num_of_clauses:                    1537
% 2.52/0.98  prop_preprocess_simplified:             4818
% 2.52/0.98  prop_fo_subsumed:                       53
% 2.52/0.98  prop_solver_time:                       0.
% 2.52/0.98  smt_solver_time:                        0.
% 2.52/0.98  smt_fast_solver_time:                   0.
% 2.52/0.98  prop_fast_solver_time:                  0.
% 2.52/0.98  prop_unsat_core_time:                   0.
% 2.52/0.98  
% 2.52/0.98  ------ QBF
% 2.52/0.98  
% 2.52/0.98  qbf_q_res:                              0
% 2.52/0.98  qbf_num_tautologies:                    0
% 2.52/0.98  qbf_prep_cycles:                        0
% 2.52/0.98  
% 2.52/0.98  ------ BMC1
% 2.52/0.98  
% 2.52/0.98  bmc1_current_bound:                     -1
% 2.52/0.98  bmc1_last_solved_bound:                 -1
% 2.52/0.98  bmc1_unsat_core_size:                   -1
% 2.52/0.98  bmc1_unsat_core_parents_size:           -1
% 2.52/0.98  bmc1_merge_next_fun:                    0
% 2.52/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation
% 2.52/0.98  
% 2.52/0.98  inst_num_of_clauses:                    455
% 2.52/0.98  inst_num_in_passive:                    65
% 2.52/0.98  inst_num_in_active:                     353
% 2.52/0.98  inst_num_in_unprocessed:                37
% 2.52/0.98  inst_num_of_loops:                      370
% 2.52/0.98  inst_num_of_learning_restarts:          0
% 2.52/0.98  inst_num_moves_active_passive:          11
% 2.52/0.98  inst_lit_activity:                      0
% 2.52/0.98  inst_lit_activity_moves:                0
% 2.52/0.98  inst_num_tautologies:                   0
% 2.52/0.98  inst_num_prop_implied:                  0
% 2.52/0.98  inst_num_existing_simplified:           0
% 2.52/0.98  inst_num_eq_res_simplified:             0
% 2.52/0.98  inst_num_child_elim:                    0
% 2.52/0.98  inst_num_of_dismatching_blockings:      123
% 2.52/0.98  inst_num_of_non_proper_insts:           541
% 2.52/0.98  inst_num_of_duplicates:                 0
% 2.52/0.98  inst_inst_num_from_inst_to_res:         0
% 2.52/0.98  inst_dismatching_checking_time:         0.
% 2.52/0.98  
% 2.52/0.98  ------ Resolution
% 2.52/0.98  
% 2.52/0.98  res_num_of_clauses:                     0
% 2.52/0.98  res_num_in_passive:                     0
% 2.52/0.98  res_num_in_active:                      0
% 2.52/0.98  res_num_of_loops:                       132
% 2.52/0.98  res_forward_subset_subsumed:            127
% 2.52/0.98  res_backward_subset_subsumed:           2
% 2.52/0.98  res_forward_subsumed:                   0
% 2.52/0.98  res_backward_subsumed:                  0
% 2.52/0.98  res_forward_subsumption_resolution:     0
% 2.52/0.98  res_backward_subsumption_resolution:    0
% 2.52/0.98  res_clause_to_clause_subsumption:       662
% 2.52/0.98  res_orphan_elimination:                 0
% 2.52/0.98  res_tautology_del:                      88
% 2.52/0.98  res_num_eq_res_simplified:              0
% 2.52/0.98  res_num_sel_changes:                    0
% 2.52/0.98  res_moves_from_active_to_pass:          0
% 2.52/0.98  
% 2.52/0.98  ------ Superposition
% 2.52/0.98  
% 2.52/0.98  sup_time_total:                         0.
% 2.52/0.98  sup_time_generating:                    0.
% 2.52/0.98  sup_time_sim_full:                      0.
% 2.52/0.98  sup_time_sim_immed:                     0.
% 2.52/0.98  
% 2.52/0.98  sup_num_of_clauses:                     94
% 2.52/0.98  sup_num_in_active:                      41
% 2.52/0.98  sup_num_in_passive:                     53
% 2.52/0.98  sup_num_of_loops:                       73
% 2.52/0.98  sup_fw_superposition:                   69
% 2.52/0.98  sup_bw_superposition:                   6
% 2.52/0.98  sup_immediate_simplified:               0
% 2.52/0.98  sup_given_eliminated:                   0
% 2.52/0.98  comparisons_done:                       0
% 2.52/0.98  comparisons_avoided:                    2
% 2.52/0.98  
% 2.52/0.98  ------ Simplifications
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  sim_fw_subset_subsumed:                 0
% 2.52/0.98  sim_bw_subset_subsumed:                 2
% 2.52/0.98  sim_fw_subsumed:                        0
% 2.52/0.98  sim_bw_subsumed:                        0
% 2.52/0.98  sim_fw_subsumption_res:                 11
% 2.52/0.98  sim_bw_subsumption_res:                 0
% 2.52/0.98  sim_tautology_del:                      0
% 2.52/0.98  sim_eq_tautology_del:                   0
% 2.52/0.98  sim_eq_res_simp:                        0
% 2.52/0.98  sim_fw_demodulated:                     0
% 2.52/0.98  sim_bw_demodulated:                     32
% 2.52/0.98  sim_light_normalised:                   0
% 2.52/0.98  sim_joinable_taut:                      0
% 2.52/0.98  sim_joinable_simp:                      0
% 2.52/0.98  sim_ac_normalised:                      0
% 2.52/0.98  sim_smt_subsumption:                    0
% 2.52/0.98  
%------------------------------------------------------------------------------
