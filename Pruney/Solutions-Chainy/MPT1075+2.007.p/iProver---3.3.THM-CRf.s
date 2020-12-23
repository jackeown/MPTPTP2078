%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:19 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  250 (1101 expanded)
%              Number of clauses        :  161 ( 309 expanded)
%              Number of leaves         :   25 ( 388 expanded)
%              Depth                    :   25
%              Number of atoms          :  927 (8339 expanded)
%              Number of equality atoms :  373 (1421 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK7) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK7))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK6),X5) != k1_funct_1(sK6,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK6,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                ( k3_funct_2(X1,sK4,k8_funct_2(X1,X0,sK4,sK5,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK5,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK5,X1,X0)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
                    ( k3_funct_2(sK3,X2,k8_funct_2(sK3,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK3,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK3) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
            & v1_funct_2(X3,sK3,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK2,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK2,X3,X5))
                      & v1_partfun1(X4,sK2)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
              & v1_funct_2(X3,X1,sK2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7))
    & v1_partfun1(sK6,sK2)
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f42,f59,f58,f57,f56,f55])).

fof(f99,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f100,plain,(
    v1_partfun1(sK6,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
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

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7)) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1266,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1265,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1274,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2927,plain,
    ( k1_relset_1(sK2,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1265,c_1274])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1263,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1273,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2849,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1263,c_1273])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1268,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3160,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_1268])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3589,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3160,c_41,c_43,c_44,c_45])).

cnf(c_3590,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3589])).

cnf(c_3601,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_3590])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1594,plain,
    ( v5_relat_1(sK5,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1595,plain,
    ( v5_relat_1(sK5,sK2) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_2023,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2022])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2451,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2452,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2451])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3775,plain,
    ( ~ v5_relat_1(sK5,sK2)
    | r1_tarski(k2_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3776,plain,
    ( v5_relat_1(sK5,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3775])).

cnf(c_1281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4004,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1281])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_2020,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_2448,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2449,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_4024,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4004,c_47,c_2020,c_2449])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,negated_conjecture,
    ( v1_partfun1(sK6,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_422,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK6 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_423,plain,
    ( ~ v4_relat_1(sK6,sK2)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK2 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK2
    | sK6 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_423])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK2 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_668,plain,
    ( ~ v1_relat_1(sK6)
    | sP0_iProver_split
    | k1_relat_1(sK6) = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_440])).

cnf(c_1257,plain,
    ( k1_relat_1(sK6) = sK2
    | v1_relat_1(sK6) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_4029,plain,
    ( k1_relat_1(sK6) = sK2
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_1257])).

cnf(c_667,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_440])).

cnf(c_1258,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1988,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1258])).

cnf(c_1998,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1988])).

cnf(c_4860,plain,
    ( k1_relat_1(sK6) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_34,c_668,c_1998,c_2019,c_2448])).

cnf(c_4863,plain,
    ( k1_relset_1(sK2,sK4,sK6) = sK2 ),
    inference(demodulation,[status(thm)],[c_4860,c_2927])).

cnf(c_4866,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_3590])).

cnf(c_5093,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | sK3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3601,c_45,c_46,c_47,c_1595,c_2023,c_2452,c_3776,c_4866])).

cnf(c_5094,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5093])).

cnf(c_5103,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1266,c_5094])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1272,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1269,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5788,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_1269])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1270,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1271,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22821,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5788,c_1270,c_1271])).

cnf(c_22828,plain,
    ( k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_22821])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_42,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_23309,plain,
    ( v1_funct_1(X1) != iProver_top
    | k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22828,c_42,c_43,c_44])).

cnf(c_23310,plain,
    ( k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_23309])).

cnf(c_23321,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_23310])).

cnf(c_1654,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X3,X0,sK6))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1890,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k8_funct_2(X0,X1,X2,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_2472,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_3905,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2472])).

cnf(c_3906,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3905])).

cnf(c_1674,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X3,X0,sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1950,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | m1_subset_1(k8_funct_2(X0,X1,X2,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_2491,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | m1_subset_1(k8_funct_2(sK3,sK2,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_3945,plain,
    ( ~ v1_funct_2(sK5,sK3,sK2)
    | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_3946,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3945])).

cnf(c_1684,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,sK6),X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1970,plain,
    ( v1_funct_2(k8_funct_2(X0,X1,X2,sK5,sK6),X0,X2)
    | ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_2521,plain,
    ( v1_funct_2(k8_funct_2(sK3,sK2,X0,sK5,sK6),sK3,X0)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_3948,plain,
    ( v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_3949,plain,
    ( v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4) = iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3948])).

cnf(c_7123,plain,
    ( ~ v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | ~ v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
    | k3_funct_2(X0,X1,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X2) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_15955,plain,
    ( ~ v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4)
    | ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK3)
    | ~ v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
    | k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_7123])).

cnf(c_15956,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
    | v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15955])).

cnf(c_23385,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23321,c_42,c_43,c_44,c_45,c_46,c_47,c_3906,c_3946,c_3949,c_15956])).

cnf(c_23386,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_23385])).

cnf(c_23394,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_1266,c_23386])).

cnf(c_3789,plain,
    ( k3_funct_2(sK3,sK2,sK5,X0) = k1_funct_1(sK5,X0)
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1269])).

cnf(c_4132,plain,
    ( k3_funct_2(sK3,sK2,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3789,c_42,c_43,c_44])).

cnf(c_4141,plain,
    ( k3_funct_2(sK3,sK2,sK5,sK7) = k1_funct_1(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_1266,c_4132])).

cnf(c_31,negated_conjecture,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4147,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_4141,c_31])).

cnf(c_23400,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_23394,c_4147])).

cnf(c_23496,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5103,c_23400])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1280,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5649,plain,
    ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
    | v5_relat_1(sK5,X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1280])).

cnf(c_1606,plain,
    ( v5_relat_1(X0,X1)
    | ~ v5_relat_1(k2_zfmisc_1(X2,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(k2_zfmisc_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2508,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK3,sK2),X0)
    | v5_relat_1(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_2509,plain,
    ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
    | v5_relat_1(sK5,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2508])).

cnf(c_6056,plain,
    ( v5_relat_1(sK5,X0) = iProver_top
    | v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5649,c_45,c_2452,c_2509])).

cnf(c_6057,plain,
    ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
    | v5_relat_1(sK5,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6056])).

cnf(c_23610,plain,
    ( v5_relat_1(k2_zfmisc_1(k1_xboole_0,sK2),X0) != iProver_top
    | v5_relat_1(sK5,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23496,c_6057])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_23670,plain,
    ( v5_relat_1(sK5,X0) = iProver_top
    | v5_relat_1(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23610,c_8])).

cnf(c_25158,plain,
    ( v5_relat_1(sK5,k1_xboole_0) = iProver_top
    | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23670])).

cnf(c_14126,plain,
    ( ~ v5_relat_1(sK5,X0)
    | r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_14132,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14126])).

cnf(c_14134,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14132])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1283,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1267,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3161,plain,
    ( v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_1267])).

cnf(c_3420,plain,
    ( r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3161,c_41,c_42,c_43,c_44,c_45])).

cnf(c_3421,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3420])).

cnf(c_4149,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK7),k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4141,c_3421])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4444,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4149,c_48])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1286,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4664,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4444,c_1286])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1276,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6193,plain,
    ( r1_tarski(X0,k1_funct_1(sK5,sK7)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4664,c_1276])).

cnf(c_11446,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_6193])).

cnf(c_672,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3695,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_3696,plain,
    ( X0 != X1
    | k2_relat_1(X2) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k2_relat_1(X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3695])).

cnf(c_3698,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3696])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1277,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2230,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1277])).

cnf(c_105,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_107,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_95,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_97,plain,
    ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25158,c_14134,c_11446,c_3698,c_2452,c_2230,c_2023,c_107,c_104,c_103,c_97,c_16,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.81/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.47  
% 7.81/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.47  
% 7.81/1.47  ------  iProver source info
% 7.81/1.47  
% 7.81/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.47  git: non_committed_changes: false
% 7.81/1.47  git: last_make_outside_of_git: false
% 7.81/1.47  
% 7.81/1.47  ------ 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options
% 7.81/1.47  
% 7.81/1.47  --out_options                           all
% 7.81/1.47  --tptp_safe_out                         true
% 7.81/1.47  --problem_path                          ""
% 7.81/1.47  --include_path                          ""
% 7.81/1.47  --clausifier                            res/vclausify_rel
% 7.81/1.47  --clausifier_options                    --mode clausify
% 7.81/1.47  --stdin                                 false
% 7.81/1.47  --stats_out                             all
% 7.81/1.47  
% 7.81/1.47  ------ General Options
% 7.81/1.47  
% 7.81/1.47  --fof                                   false
% 7.81/1.47  --time_out_real                         305.
% 7.81/1.47  --time_out_virtual                      -1.
% 7.81/1.47  --symbol_type_check                     false
% 7.81/1.47  --clausify_out                          false
% 7.81/1.47  --sig_cnt_out                           false
% 7.81/1.47  --trig_cnt_out                          false
% 7.81/1.47  --trig_cnt_out_tolerance                1.
% 7.81/1.47  --trig_cnt_out_sk_spl                   false
% 7.81/1.47  --abstr_cl_out                          false
% 7.81/1.47  
% 7.81/1.47  ------ Global Options
% 7.81/1.47  
% 7.81/1.47  --schedule                              default
% 7.81/1.47  --add_important_lit                     false
% 7.81/1.47  --prop_solver_per_cl                    1000
% 7.81/1.47  --min_unsat_core                        false
% 7.81/1.47  --soft_assumptions                      false
% 7.81/1.47  --soft_lemma_size                       3
% 7.81/1.47  --prop_impl_unit_size                   0
% 7.81/1.47  --prop_impl_unit                        []
% 7.81/1.47  --share_sel_clauses                     true
% 7.81/1.47  --reset_solvers                         false
% 7.81/1.47  --bc_imp_inh                            [conj_cone]
% 7.81/1.47  --conj_cone_tolerance                   3.
% 7.81/1.47  --extra_neg_conj                        none
% 7.81/1.47  --large_theory_mode                     true
% 7.81/1.47  --prolific_symb_bound                   200
% 7.81/1.47  --lt_threshold                          2000
% 7.81/1.47  --clause_weak_htbl                      true
% 7.81/1.47  --gc_record_bc_elim                     false
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing Options
% 7.81/1.47  
% 7.81/1.47  --preprocessing_flag                    true
% 7.81/1.47  --time_out_prep_mult                    0.1
% 7.81/1.47  --splitting_mode                        input
% 7.81/1.47  --splitting_grd                         true
% 7.81/1.47  --splitting_cvd                         false
% 7.81/1.47  --splitting_cvd_svl                     false
% 7.81/1.47  --splitting_nvd                         32
% 7.81/1.47  --sub_typing                            true
% 7.81/1.47  --prep_gs_sim                           true
% 7.81/1.47  --prep_unflatten                        true
% 7.81/1.47  --prep_res_sim                          true
% 7.81/1.47  --prep_upred                            true
% 7.81/1.47  --prep_sem_filter                       exhaustive
% 7.81/1.47  --prep_sem_filter_out                   false
% 7.81/1.47  --pred_elim                             true
% 7.81/1.47  --res_sim_input                         true
% 7.81/1.47  --eq_ax_congr_red                       true
% 7.81/1.47  --pure_diseq_elim                       true
% 7.81/1.47  --brand_transform                       false
% 7.81/1.47  --non_eq_to_eq                          false
% 7.81/1.47  --prep_def_merge                        true
% 7.81/1.47  --prep_def_merge_prop_impl              false
% 7.81/1.47  --prep_def_merge_mbd                    true
% 7.81/1.47  --prep_def_merge_tr_red                 false
% 7.81/1.47  --prep_def_merge_tr_cl                  false
% 7.81/1.47  --smt_preprocessing                     true
% 7.81/1.47  --smt_ac_axioms                         fast
% 7.81/1.47  --preprocessed_out                      false
% 7.81/1.47  --preprocessed_stats                    false
% 7.81/1.47  
% 7.81/1.47  ------ Abstraction refinement Options
% 7.81/1.47  
% 7.81/1.47  --abstr_ref                             []
% 7.81/1.47  --abstr_ref_prep                        false
% 7.81/1.47  --abstr_ref_until_sat                   false
% 7.81/1.47  --abstr_ref_sig_restrict                funpre
% 7.81/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.47  --abstr_ref_under                       []
% 7.81/1.47  
% 7.81/1.47  ------ SAT Options
% 7.81/1.47  
% 7.81/1.47  --sat_mode                              false
% 7.81/1.47  --sat_fm_restart_options                ""
% 7.81/1.47  --sat_gr_def                            false
% 7.81/1.47  --sat_epr_types                         true
% 7.81/1.47  --sat_non_cyclic_types                  false
% 7.81/1.47  --sat_finite_models                     false
% 7.81/1.47  --sat_fm_lemmas                         false
% 7.81/1.47  --sat_fm_prep                           false
% 7.81/1.47  --sat_fm_uc_incr                        true
% 7.81/1.47  --sat_out_model                         small
% 7.81/1.47  --sat_out_clauses                       false
% 7.81/1.47  
% 7.81/1.47  ------ QBF Options
% 7.81/1.47  
% 7.81/1.47  --qbf_mode                              false
% 7.81/1.47  --qbf_elim_univ                         false
% 7.81/1.47  --qbf_dom_inst                          none
% 7.81/1.47  --qbf_dom_pre_inst                      false
% 7.81/1.47  --qbf_sk_in                             false
% 7.81/1.47  --qbf_pred_elim                         true
% 7.81/1.47  --qbf_split                             512
% 7.81/1.47  
% 7.81/1.47  ------ BMC1 Options
% 7.81/1.47  
% 7.81/1.47  --bmc1_incremental                      false
% 7.81/1.47  --bmc1_axioms                           reachable_all
% 7.81/1.47  --bmc1_min_bound                        0
% 7.81/1.47  --bmc1_max_bound                        -1
% 7.81/1.47  --bmc1_max_bound_default                -1
% 7.81/1.47  --bmc1_symbol_reachability              true
% 7.81/1.47  --bmc1_property_lemmas                  false
% 7.81/1.47  --bmc1_k_induction                      false
% 7.81/1.47  --bmc1_non_equiv_states                 false
% 7.81/1.47  --bmc1_deadlock                         false
% 7.81/1.47  --bmc1_ucm                              false
% 7.81/1.47  --bmc1_add_unsat_core                   none
% 7.81/1.47  --bmc1_unsat_core_children              false
% 7.81/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.47  --bmc1_out_stat                         full
% 7.81/1.47  --bmc1_ground_init                      false
% 7.81/1.47  --bmc1_pre_inst_next_state              false
% 7.81/1.47  --bmc1_pre_inst_state                   false
% 7.81/1.47  --bmc1_pre_inst_reach_state             false
% 7.81/1.47  --bmc1_out_unsat_core                   false
% 7.81/1.47  --bmc1_aig_witness_out                  false
% 7.81/1.47  --bmc1_verbose                          false
% 7.81/1.47  --bmc1_dump_clauses_tptp                false
% 7.81/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.47  --bmc1_dump_file                        -
% 7.81/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.47  --bmc1_ucm_extend_mode                  1
% 7.81/1.47  --bmc1_ucm_init_mode                    2
% 7.81/1.47  --bmc1_ucm_cone_mode                    none
% 7.81/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.47  --bmc1_ucm_relax_model                  4
% 7.81/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.47  --bmc1_ucm_layered_model                none
% 7.81/1.47  --bmc1_ucm_max_lemma_size               10
% 7.81/1.47  
% 7.81/1.47  ------ AIG Options
% 7.81/1.47  
% 7.81/1.47  --aig_mode                              false
% 7.81/1.47  
% 7.81/1.47  ------ Instantiation Options
% 7.81/1.47  
% 7.81/1.47  --instantiation_flag                    true
% 7.81/1.47  --inst_sos_flag                         false
% 7.81/1.47  --inst_sos_phase                        true
% 7.81/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel_side                     num_symb
% 7.81/1.47  --inst_solver_per_active                1400
% 7.81/1.47  --inst_solver_calls_frac                1.
% 7.81/1.47  --inst_passive_queue_type               priority_queues
% 7.81/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.47  --inst_passive_queues_freq              [25;2]
% 7.81/1.47  --inst_dismatching                      true
% 7.81/1.47  --inst_eager_unprocessed_to_passive     true
% 7.81/1.47  --inst_prop_sim_given                   true
% 7.81/1.47  --inst_prop_sim_new                     false
% 7.81/1.47  --inst_subs_new                         false
% 7.81/1.47  --inst_eq_res_simp                      false
% 7.81/1.47  --inst_subs_given                       false
% 7.81/1.47  --inst_orphan_elimination               true
% 7.81/1.47  --inst_learning_loop_flag               true
% 7.81/1.47  --inst_learning_start                   3000
% 7.81/1.47  --inst_learning_factor                  2
% 7.81/1.47  --inst_start_prop_sim_after_learn       3
% 7.81/1.47  --inst_sel_renew                        solver
% 7.81/1.47  --inst_lit_activity_flag                true
% 7.81/1.47  --inst_restr_to_given                   false
% 7.81/1.47  --inst_activity_threshold               500
% 7.81/1.47  --inst_out_proof                        true
% 7.81/1.47  
% 7.81/1.47  ------ Resolution Options
% 7.81/1.47  
% 7.81/1.47  --resolution_flag                       true
% 7.81/1.47  --res_lit_sel                           adaptive
% 7.81/1.47  --res_lit_sel_side                      none
% 7.81/1.47  --res_ordering                          kbo
% 7.81/1.47  --res_to_prop_solver                    active
% 7.81/1.47  --res_prop_simpl_new                    false
% 7.81/1.47  --res_prop_simpl_given                  true
% 7.81/1.47  --res_passive_queue_type                priority_queues
% 7.81/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.47  --res_passive_queues_freq               [15;5]
% 7.81/1.47  --res_forward_subs                      full
% 7.81/1.47  --res_backward_subs                     full
% 7.81/1.47  --res_forward_subs_resolution           true
% 7.81/1.47  --res_backward_subs_resolution          true
% 7.81/1.47  --res_orphan_elimination                true
% 7.81/1.47  --res_time_limit                        2.
% 7.81/1.47  --res_out_proof                         true
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Options
% 7.81/1.47  
% 7.81/1.47  --superposition_flag                    true
% 7.81/1.47  --sup_passive_queue_type                priority_queues
% 7.81/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.47  --demod_completeness_check              fast
% 7.81/1.47  --demod_use_ground                      true
% 7.81/1.47  --sup_to_prop_solver                    passive
% 7.81/1.47  --sup_prop_simpl_new                    true
% 7.81/1.47  --sup_prop_simpl_given                  true
% 7.81/1.47  --sup_fun_splitting                     false
% 7.81/1.47  --sup_smt_interval                      50000
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Simplification Setup
% 7.81/1.47  
% 7.81/1.47  --sup_indices_passive                   []
% 7.81/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_full_bw                           [BwDemod]
% 7.81/1.47  --sup_immed_triv                        [TrivRules]
% 7.81/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_immed_bw_main                     []
% 7.81/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  
% 7.81/1.47  ------ Combination Options
% 7.81/1.47  
% 7.81/1.47  --comb_res_mult                         3
% 7.81/1.47  --comb_sup_mult                         2
% 7.81/1.47  --comb_inst_mult                        10
% 7.81/1.47  
% 7.81/1.47  ------ Debug Options
% 7.81/1.47  
% 7.81/1.47  --dbg_backtrace                         false
% 7.81/1.47  --dbg_dump_prop_clauses                 false
% 7.81/1.47  --dbg_dump_prop_clauses_file            -
% 7.81/1.47  --dbg_out_stat                          false
% 7.81/1.47  ------ Parsing...
% 7.81/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.47  ------ Proving...
% 7.81/1.47  ------ Problem Properties 
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  clauses                                 38
% 7.81/1.47  conjectures                             9
% 7.81/1.47  EPR                                     11
% 7.81/1.47  Horn                                    32
% 7.81/1.47  unary                                   17
% 7.81/1.47  binary                                  7
% 7.81/1.47  lits                                    97
% 7.81/1.47  lits eq                                 15
% 7.81/1.47  fd_pure                                 0
% 7.81/1.47  fd_pseudo                               0
% 7.81/1.47  fd_cond                                 2
% 7.81/1.47  fd_pseudo_cond                          1
% 7.81/1.47  AC symbols                              0
% 7.81/1.47  
% 7.81/1.47  ------ Schedule dynamic 5 is on 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  ------ 
% 7.81/1.47  Current options:
% 7.81/1.47  ------ 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options
% 7.81/1.47  
% 7.81/1.47  --out_options                           all
% 7.81/1.47  --tptp_safe_out                         true
% 7.81/1.47  --problem_path                          ""
% 7.81/1.47  --include_path                          ""
% 7.81/1.47  --clausifier                            res/vclausify_rel
% 7.81/1.47  --clausifier_options                    --mode clausify
% 7.81/1.47  --stdin                                 false
% 7.81/1.47  --stats_out                             all
% 7.81/1.47  
% 7.81/1.47  ------ General Options
% 7.81/1.47  
% 7.81/1.47  --fof                                   false
% 7.81/1.47  --time_out_real                         305.
% 7.81/1.47  --time_out_virtual                      -1.
% 7.81/1.47  --symbol_type_check                     false
% 7.81/1.47  --clausify_out                          false
% 7.81/1.47  --sig_cnt_out                           false
% 7.81/1.47  --trig_cnt_out                          false
% 7.81/1.47  --trig_cnt_out_tolerance                1.
% 7.81/1.47  --trig_cnt_out_sk_spl                   false
% 7.81/1.47  --abstr_cl_out                          false
% 7.81/1.47  
% 7.81/1.47  ------ Global Options
% 7.81/1.47  
% 7.81/1.47  --schedule                              default
% 7.81/1.47  --add_important_lit                     false
% 7.81/1.47  --prop_solver_per_cl                    1000
% 7.81/1.47  --min_unsat_core                        false
% 7.81/1.47  --soft_assumptions                      false
% 7.81/1.47  --soft_lemma_size                       3
% 7.81/1.47  --prop_impl_unit_size                   0
% 7.81/1.47  --prop_impl_unit                        []
% 7.81/1.47  --share_sel_clauses                     true
% 7.81/1.47  --reset_solvers                         false
% 7.81/1.47  --bc_imp_inh                            [conj_cone]
% 7.81/1.47  --conj_cone_tolerance                   3.
% 7.81/1.47  --extra_neg_conj                        none
% 7.81/1.47  --large_theory_mode                     true
% 7.81/1.47  --prolific_symb_bound                   200
% 7.81/1.47  --lt_threshold                          2000
% 7.81/1.47  --clause_weak_htbl                      true
% 7.81/1.47  --gc_record_bc_elim                     false
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing Options
% 7.81/1.47  
% 7.81/1.47  --preprocessing_flag                    true
% 7.81/1.47  --time_out_prep_mult                    0.1
% 7.81/1.47  --splitting_mode                        input
% 7.81/1.47  --splitting_grd                         true
% 7.81/1.47  --splitting_cvd                         false
% 7.81/1.47  --splitting_cvd_svl                     false
% 7.81/1.47  --splitting_nvd                         32
% 7.81/1.47  --sub_typing                            true
% 7.81/1.47  --prep_gs_sim                           true
% 7.81/1.47  --prep_unflatten                        true
% 7.81/1.47  --prep_res_sim                          true
% 7.81/1.47  --prep_upred                            true
% 7.81/1.47  --prep_sem_filter                       exhaustive
% 7.81/1.47  --prep_sem_filter_out                   false
% 7.81/1.47  --pred_elim                             true
% 7.81/1.47  --res_sim_input                         true
% 7.81/1.47  --eq_ax_congr_red                       true
% 7.81/1.47  --pure_diseq_elim                       true
% 7.81/1.47  --brand_transform                       false
% 7.81/1.47  --non_eq_to_eq                          false
% 7.81/1.47  --prep_def_merge                        true
% 7.81/1.47  --prep_def_merge_prop_impl              false
% 7.81/1.47  --prep_def_merge_mbd                    true
% 7.81/1.47  --prep_def_merge_tr_red                 false
% 7.81/1.47  --prep_def_merge_tr_cl                  false
% 7.81/1.47  --smt_preprocessing                     true
% 7.81/1.47  --smt_ac_axioms                         fast
% 7.81/1.47  --preprocessed_out                      false
% 7.81/1.47  --preprocessed_stats                    false
% 7.81/1.47  
% 7.81/1.47  ------ Abstraction refinement Options
% 7.81/1.47  
% 7.81/1.47  --abstr_ref                             []
% 7.81/1.47  --abstr_ref_prep                        false
% 7.81/1.47  --abstr_ref_until_sat                   false
% 7.81/1.47  --abstr_ref_sig_restrict                funpre
% 7.81/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.47  --abstr_ref_under                       []
% 7.81/1.47  
% 7.81/1.47  ------ SAT Options
% 7.81/1.47  
% 7.81/1.47  --sat_mode                              false
% 7.81/1.47  --sat_fm_restart_options                ""
% 7.81/1.47  --sat_gr_def                            false
% 7.81/1.47  --sat_epr_types                         true
% 7.81/1.47  --sat_non_cyclic_types                  false
% 7.81/1.47  --sat_finite_models                     false
% 7.81/1.47  --sat_fm_lemmas                         false
% 7.81/1.47  --sat_fm_prep                           false
% 7.81/1.47  --sat_fm_uc_incr                        true
% 7.81/1.47  --sat_out_model                         small
% 7.81/1.47  --sat_out_clauses                       false
% 7.81/1.47  
% 7.81/1.47  ------ QBF Options
% 7.81/1.47  
% 7.81/1.47  --qbf_mode                              false
% 7.81/1.47  --qbf_elim_univ                         false
% 7.81/1.47  --qbf_dom_inst                          none
% 7.81/1.47  --qbf_dom_pre_inst                      false
% 7.81/1.47  --qbf_sk_in                             false
% 7.81/1.47  --qbf_pred_elim                         true
% 7.81/1.47  --qbf_split                             512
% 7.81/1.47  
% 7.81/1.47  ------ BMC1 Options
% 7.81/1.47  
% 7.81/1.47  --bmc1_incremental                      false
% 7.81/1.47  --bmc1_axioms                           reachable_all
% 7.81/1.47  --bmc1_min_bound                        0
% 7.81/1.47  --bmc1_max_bound                        -1
% 7.81/1.47  --bmc1_max_bound_default                -1
% 7.81/1.47  --bmc1_symbol_reachability              true
% 7.81/1.47  --bmc1_property_lemmas                  false
% 7.81/1.47  --bmc1_k_induction                      false
% 7.81/1.47  --bmc1_non_equiv_states                 false
% 7.81/1.47  --bmc1_deadlock                         false
% 7.81/1.47  --bmc1_ucm                              false
% 7.81/1.47  --bmc1_add_unsat_core                   none
% 7.81/1.47  --bmc1_unsat_core_children              false
% 7.81/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.47  --bmc1_out_stat                         full
% 7.81/1.47  --bmc1_ground_init                      false
% 7.81/1.47  --bmc1_pre_inst_next_state              false
% 7.81/1.47  --bmc1_pre_inst_state                   false
% 7.81/1.47  --bmc1_pre_inst_reach_state             false
% 7.81/1.47  --bmc1_out_unsat_core                   false
% 7.81/1.47  --bmc1_aig_witness_out                  false
% 7.81/1.47  --bmc1_verbose                          false
% 7.81/1.47  --bmc1_dump_clauses_tptp                false
% 7.81/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.47  --bmc1_dump_file                        -
% 7.81/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.47  --bmc1_ucm_extend_mode                  1
% 7.81/1.47  --bmc1_ucm_init_mode                    2
% 7.81/1.47  --bmc1_ucm_cone_mode                    none
% 7.81/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.47  --bmc1_ucm_relax_model                  4
% 7.81/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.47  --bmc1_ucm_layered_model                none
% 7.81/1.47  --bmc1_ucm_max_lemma_size               10
% 7.81/1.47  
% 7.81/1.47  ------ AIG Options
% 7.81/1.47  
% 7.81/1.47  --aig_mode                              false
% 7.81/1.47  
% 7.81/1.47  ------ Instantiation Options
% 7.81/1.47  
% 7.81/1.47  --instantiation_flag                    true
% 7.81/1.47  --inst_sos_flag                         false
% 7.81/1.47  --inst_sos_phase                        true
% 7.81/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel_side                     none
% 7.81/1.47  --inst_solver_per_active                1400
% 7.81/1.47  --inst_solver_calls_frac                1.
% 7.81/1.47  --inst_passive_queue_type               priority_queues
% 7.81/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.47  --inst_passive_queues_freq              [25;2]
% 7.81/1.47  --inst_dismatching                      true
% 7.81/1.47  --inst_eager_unprocessed_to_passive     true
% 7.81/1.47  --inst_prop_sim_given                   true
% 7.81/1.47  --inst_prop_sim_new                     false
% 7.81/1.47  --inst_subs_new                         false
% 7.81/1.47  --inst_eq_res_simp                      false
% 7.81/1.47  --inst_subs_given                       false
% 7.81/1.47  --inst_orphan_elimination               true
% 7.81/1.47  --inst_learning_loop_flag               true
% 7.81/1.47  --inst_learning_start                   3000
% 7.81/1.47  --inst_learning_factor                  2
% 7.81/1.47  --inst_start_prop_sim_after_learn       3
% 7.81/1.47  --inst_sel_renew                        solver
% 7.81/1.47  --inst_lit_activity_flag                true
% 7.81/1.47  --inst_restr_to_given                   false
% 7.81/1.47  --inst_activity_threshold               500
% 7.81/1.47  --inst_out_proof                        true
% 7.81/1.47  
% 7.81/1.47  ------ Resolution Options
% 7.81/1.47  
% 7.81/1.47  --resolution_flag                       false
% 7.81/1.47  --res_lit_sel                           adaptive
% 7.81/1.47  --res_lit_sel_side                      none
% 7.81/1.47  --res_ordering                          kbo
% 7.81/1.47  --res_to_prop_solver                    active
% 7.81/1.47  --res_prop_simpl_new                    false
% 7.81/1.47  --res_prop_simpl_given                  true
% 7.81/1.47  --res_passive_queue_type                priority_queues
% 7.81/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.47  --res_passive_queues_freq               [15;5]
% 7.81/1.47  --res_forward_subs                      full
% 7.81/1.47  --res_backward_subs                     full
% 7.81/1.47  --res_forward_subs_resolution           true
% 7.81/1.47  --res_backward_subs_resolution          true
% 7.81/1.47  --res_orphan_elimination                true
% 7.81/1.47  --res_time_limit                        2.
% 7.81/1.47  --res_out_proof                         true
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Options
% 7.81/1.47  
% 7.81/1.47  --superposition_flag                    true
% 7.81/1.47  --sup_passive_queue_type                priority_queues
% 7.81/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.47  --demod_completeness_check              fast
% 7.81/1.47  --demod_use_ground                      true
% 7.81/1.47  --sup_to_prop_solver                    passive
% 7.81/1.47  --sup_prop_simpl_new                    true
% 7.81/1.47  --sup_prop_simpl_given                  true
% 7.81/1.47  --sup_fun_splitting                     false
% 7.81/1.47  --sup_smt_interval                      50000
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Simplification Setup
% 7.81/1.47  
% 7.81/1.47  --sup_indices_passive                   []
% 7.81/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_full_bw                           [BwDemod]
% 7.81/1.47  --sup_immed_triv                        [TrivRules]
% 7.81/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_immed_bw_main                     []
% 7.81/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  
% 7.81/1.47  ------ Combination Options
% 7.81/1.47  
% 7.81/1.47  --comb_res_mult                         3
% 7.81/1.47  --comb_sup_mult                         2
% 7.81/1.47  --comb_inst_mult                        10
% 7.81/1.47  
% 7.81/1.47  ------ Debug Options
% 7.81/1.47  
% 7.81/1.47  --dbg_backtrace                         false
% 7.81/1.47  --dbg_dump_prop_clauses                 false
% 7.81/1.47  --dbg_dump_prop_clauses_file            -
% 7.81/1.47  --dbg_out_stat                          false
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  ------ Proving...
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  % SZS status Theorem for theBenchmark.p
% 7.81/1.47  
% 7.81/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.47  
% 7.81/1.47  fof(f20,conjecture,(
% 7.81/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f21,negated_conjecture,(
% 7.81/1.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 7.81/1.47    inference(negated_conjecture,[],[f20])).
% 7.81/1.47  
% 7.81/1.47  fof(f41,plain,(
% 7.81/1.47    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.81/1.47    inference(ennf_transformation,[],[f21])).
% 7.81/1.47  
% 7.81/1.47  fof(f42,plain,(
% 7.81/1.47    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.81/1.47    inference(flattening,[],[f41])).
% 7.81/1.47  
% 7.81/1.47  fof(f59,plain,(
% 7.81/1.47    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK7) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK7)) & v1_partfun1(X4,X0) & m1_subset_1(sK7,X1))) )),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f58,plain,(
% 7.81/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK6),X5) != k1_funct_1(sK6,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK6,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK6))) )),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f57,plain,(
% 7.81/1.47    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK4,k8_funct_2(X1,X0,sK4,sK5,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK5,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f56,plain,(
% 7.81/1.47    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK3,X2,k8_funct_2(sK3,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK3,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) & v1_funct_2(X3,sK3,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f55,plain,(
% 7.81/1.47    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK2,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK2,X3,X5)) & v1_partfun1(X4,sK2) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) & v1_funct_2(X3,X1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f60,plain,(
% 7.81/1.47    ((((k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7)) & v1_partfun1(sK6,sK2) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.81/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f42,f59,f58,f57,f56,f55])).
% 7.81/1.47  
% 7.81/1.47  fof(f99,plain,(
% 7.81/1.47    m1_subset_1(sK7,sK3)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f98,plain,(
% 7.81/1.47    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f13,axiom,(
% 7.81/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f29,plain,(
% 7.81/1.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.47    inference(ennf_transformation,[],[f13])).
% 7.81/1.47  
% 7.81/1.47  fof(f82,plain,(
% 7.81/1.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.47    inference(cnf_transformation,[],[f29])).
% 7.81/1.47  
% 7.81/1.47  fof(f96,plain,(
% 7.81/1.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f14,axiom,(
% 7.81/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f30,plain,(
% 7.81/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.47    inference(ennf_transformation,[],[f14])).
% 7.81/1.47  
% 7.81/1.47  fof(f83,plain,(
% 7.81/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.47    inference(cnf_transformation,[],[f30])).
% 7.81/1.47  
% 7.81/1.47  fof(f18,axiom,(
% 7.81/1.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f37,plain,(
% 7.81/1.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.81/1.47    inference(ennf_transformation,[],[f18])).
% 7.81/1.47  
% 7.81/1.47  fof(f38,plain,(
% 7.81/1.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.81/1.47    inference(flattening,[],[f37])).
% 7.81/1.47  
% 7.81/1.47  fof(f90,plain,(
% 7.81/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f38])).
% 7.81/1.47  
% 7.81/1.47  fof(f92,plain,(
% 7.81/1.47    ~v1_xboole_0(sK2)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f94,plain,(
% 7.81/1.47    v1_funct_1(sK5)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f95,plain,(
% 7.81/1.47    v1_funct_2(sK5,sK3,sK2)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f97,plain,(
% 7.81/1.47    v1_funct_1(sK6)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f12,axiom,(
% 7.81/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f28,plain,(
% 7.81/1.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.47    inference(ennf_transformation,[],[f12])).
% 7.81/1.47  
% 7.81/1.47  fof(f81,plain,(
% 7.81/1.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.47    inference(cnf_transformation,[],[f28])).
% 7.81/1.47  
% 7.81/1.47  fof(f6,axiom,(
% 7.81/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f23,plain,(
% 7.81/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.81/1.47    inference(ennf_transformation,[],[f6])).
% 7.81/1.47  
% 7.81/1.47  fof(f72,plain,(
% 7.81/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f23])).
% 7.81/1.47  
% 7.81/1.47  fof(f9,axiom,(
% 7.81/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f76,plain,(
% 7.81/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.81/1.47    inference(cnf_transformation,[],[f9])).
% 7.81/1.47  
% 7.81/1.47  fof(f8,axiom,(
% 7.81/1.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f26,plain,(
% 7.81/1.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.81/1.47    inference(ennf_transformation,[],[f8])).
% 7.81/1.47  
% 7.81/1.47  fof(f53,plain,(
% 7.81/1.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.81/1.47    inference(nnf_transformation,[],[f26])).
% 7.81/1.47  
% 7.81/1.47  fof(f74,plain,(
% 7.81/1.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f53])).
% 7.81/1.47  
% 7.81/1.47  fof(f80,plain,(
% 7.81/1.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.47    inference(cnf_transformation,[],[f28])).
% 7.81/1.47  
% 7.81/1.47  fof(f15,axiom,(
% 7.81/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f31,plain,(
% 7.81/1.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.81/1.47    inference(ennf_transformation,[],[f15])).
% 7.81/1.47  
% 7.81/1.47  fof(f32,plain,(
% 7.81/1.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.47    inference(flattening,[],[f31])).
% 7.81/1.47  
% 7.81/1.47  fof(f54,plain,(
% 7.81/1.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.47    inference(nnf_transformation,[],[f32])).
% 7.81/1.47  
% 7.81/1.47  fof(f84,plain,(
% 7.81/1.47    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f54])).
% 7.81/1.47  
% 7.81/1.47  fof(f100,plain,(
% 7.81/1.47    v1_partfun1(sK6,sK2)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f16,axiom,(
% 7.81/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f33,plain,(
% 7.81/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.81/1.47    inference(ennf_transformation,[],[f16])).
% 7.81/1.47  
% 7.81/1.47  fof(f34,plain,(
% 7.81/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.81/1.47    inference(flattening,[],[f33])).
% 7.81/1.47  
% 7.81/1.47  fof(f88,plain,(
% 7.81/1.47    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f34])).
% 7.81/1.47  
% 7.81/1.47  fof(f17,axiom,(
% 7.81/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f35,plain,(
% 7.81/1.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.81/1.47    inference(ennf_transformation,[],[f17])).
% 7.81/1.47  
% 7.81/1.47  fof(f36,plain,(
% 7.81/1.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.81/1.47    inference(flattening,[],[f35])).
% 7.81/1.47  
% 7.81/1.47  fof(f89,plain,(
% 7.81/1.47    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f36])).
% 7.81/1.47  
% 7.81/1.47  fof(f86,plain,(
% 7.81/1.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f34])).
% 7.81/1.47  
% 7.81/1.47  fof(f87,plain,(
% 7.81/1.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f34])).
% 7.81/1.47  
% 7.81/1.47  fof(f93,plain,(
% 7.81/1.47    ~v1_xboole_0(sK3)),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f101,plain,(
% 7.81/1.47    k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7))),
% 7.81/1.47    inference(cnf_transformation,[],[f60])).
% 7.81/1.47  
% 7.81/1.47  fof(f7,axiom,(
% 7.81/1.47    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f24,plain,(
% 7.81/1.47    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.81/1.47    inference(ennf_transformation,[],[f7])).
% 7.81/1.47  
% 7.81/1.47  fof(f25,plain,(
% 7.81/1.47    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.47    inference(flattening,[],[f24])).
% 7.81/1.47  
% 7.81/1.47  fof(f73,plain,(
% 7.81/1.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f25])).
% 7.81/1.47  
% 7.81/1.47  fof(f4,axiom,(
% 7.81/1.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f49,plain,(
% 7.81/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.81/1.47    inference(nnf_transformation,[],[f4])).
% 7.81/1.47  
% 7.81/1.47  fof(f50,plain,(
% 7.81/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.81/1.47    inference(flattening,[],[f49])).
% 7.81/1.47  
% 7.81/1.47  fof(f69,plain,(
% 7.81/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.81/1.47    inference(cnf_transformation,[],[f50])).
% 7.81/1.47  
% 7.81/1.47  fof(f105,plain,(
% 7.81/1.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.81/1.47    inference(equality_resolution,[],[f69])).
% 7.81/1.47  
% 7.81/1.47  fof(f3,axiom,(
% 7.81/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f67,plain,(
% 7.81/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f3])).
% 7.81/1.47  
% 7.81/1.47  fof(f19,axiom,(
% 7.81/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f39,plain,(
% 7.81/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.81/1.47    inference(ennf_transformation,[],[f19])).
% 7.81/1.47  
% 7.81/1.47  fof(f40,plain,(
% 7.81/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.81/1.47    inference(flattening,[],[f39])).
% 7.81/1.47  
% 7.81/1.47  fof(f91,plain,(
% 7.81/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f40])).
% 7.81/1.47  
% 7.81/1.47  fof(f1,axiom,(
% 7.81/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f22,plain,(
% 7.81/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.81/1.47    inference(ennf_transformation,[],[f1])).
% 7.81/1.47  
% 7.81/1.47  fof(f43,plain,(
% 7.81/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.47    inference(nnf_transformation,[],[f22])).
% 7.81/1.47  
% 7.81/1.47  fof(f44,plain,(
% 7.81/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.47    inference(rectify,[],[f43])).
% 7.81/1.47  
% 7.81/1.47  fof(f45,plain,(
% 7.81/1.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.81/1.47    introduced(choice_axiom,[])).
% 7.81/1.47  
% 7.81/1.47  fof(f46,plain,(
% 7.81/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 7.81/1.47  
% 7.81/1.47  fof(f61,plain,(
% 7.81/1.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f46])).
% 7.81/1.47  
% 7.81/1.47  fof(f11,axiom,(
% 7.81/1.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f27,plain,(
% 7.81/1.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.81/1.47    inference(ennf_transformation,[],[f11])).
% 7.81/1.47  
% 7.81/1.47  fof(f79,plain,(
% 7.81/1.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f27])).
% 7.81/1.47  
% 7.81/1.47  fof(f70,plain,(
% 7.81/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.81/1.47    inference(cnf_transformation,[],[f50])).
% 7.81/1.47  
% 7.81/1.47  fof(f104,plain,(
% 7.81/1.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.81/1.47    inference(equality_resolution,[],[f70])).
% 7.81/1.47  
% 7.81/1.47  fof(f68,plain,(
% 7.81/1.47    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f50])).
% 7.81/1.47  
% 7.81/1.47  fof(f75,plain,(
% 7.81/1.47    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.81/1.47    inference(cnf_transformation,[],[f53])).
% 7.81/1.47  
% 7.81/1.47  fof(f10,axiom,(
% 7.81/1.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.81/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.47  
% 7.81/1.47  fof(f78,plain,(
% 7.81/1.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.81/1.47    inference(cnf_transformation,[],[f10])).
% 7.81/1.47  
% 7.81/1.47  cnf(c_33,negated_conjecture,
% 7.81/1.47      ( m1_subset_1(sK7,sK3) ),
% 7.81/1.47      inference(cnf_transformation,[],[f99]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1266,plain,
% 7.81/1.47      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_34,negated_conjecture,
% 7.81/1.47      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 7.81/1.47      inference(cnf_transformation,[],[f98]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1265,plain,
% 7.81/1.47      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_21,plain,
% 7.81/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1274,plain,
% 7.81/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.81/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2927,plain,
% 7.81/1.47      ( k1_relset_1(sK2,sK4,sK6) = k1_relat_1(sK6) ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1265,c_1274]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_36,negated_conjecture,
% 7.81/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 7.81/1.47      inference(cnf_transformation,[],[f96]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1263,plain,
% 7.81/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_22,plain,
% 7.81/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1273,plain,
% 7.81/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.81/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2849,plain,
% 7.81/1.47      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1263,c_1273]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_29,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X3,X1)
% 7.81/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.81/1.47      | v1_xboole_0(X2)
% 7.81/1.47      | ~ v1_funct_1(X4)
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.81/1.47      | k1_xboole_0 = X1 ),
% 7.81/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1268,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.81/1.47      | k1_xboole_0 = X0
% 7.81/1.47      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.81/1.47      | m1_subset_1(X5,X0) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.47      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.81/1.47      | v1_xboole_0(X1) = iProver_top
% 7.81/1.47      | v1_funct_1(X3) != iProver_top
% 7.81/1.47      | v1_funct_1(X4) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3160,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top
% 7.81/1.47      | v1_xboole_0(sK2) = iProver_top
% 7.81/1.47      | v1_funct_1(X1) != iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_2849,c_1268]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_40,negated_conjecture,
% 7.81/1.47      ( ~ v1_xboole_0(sK2) ),
% 7.81/1.47      inference(cnf_transformation,[],[f92]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_41,plain,
% 7.81/1.47      ( v1_xboole_0(sK2) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_38,negated_conjecture,
% 7.81/1.47      ( v1_funct_1(sK5) ),
% 7.81/1.47      inference(cnf_transformation,[],[f94]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_43,plain,
% 7.81/1.47      ( v1_funct_1(sK5) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_37,negated_conjecture,
% 7.81/1.47      ( v1_funct_2(sK5,sK3,sK2) ),
% 7.81/1.47      inference(cnf_transformation,[],[f95]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_44,plain,
% 7.81/1.47      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_45,plain,
% 7.81/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3589,plain,
% 7.81/1.47      ( v1_funct_1(X1) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_3160,c_41,c_43,c_44,c_45]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3590,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK2,X0,X1)) != iProver_top
% 7.81/1.47      | v1_funct_1(X1) != iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_3589]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3601,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_2927,c_3590]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_35,negated_conjecture,
% 7.81/1.47      ( v1_funct_1(sK6) ),
% 7.81/1.47      inference(cnf_transformation,[],[f97]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_46,plain,
% 7.81/1.47      ( v1_funct_1(sK6) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_47,plain,
% 7.81/1.47      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_19,plain,
% 7.81/1.47      ( v5_relat_1(X0,X1)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.81/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1594,plain,
% 7.81/1.47      ( v5_relat_1(sK5,sK2)
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_19]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1595,plain,
% 7.81/1.47      ( v5_relat_1(sK5,sK2) = iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_11,plain,
% 7.81/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.47      | ~ v1_relat_1(X1)
% 7.81/1.47      | v1_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1557,plain,
% 7.81/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | v1_relat_1(X0)
% 7.81/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_11]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2022,plain,
% 7.81/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
% 7.81/1.47      | v1_relat_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1557]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2023,plain,
% 7.81/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
% 7.81/1.47      | v1_relat_1(sK5) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2022]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_15,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.81/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2451,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_15]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2452,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2451]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_14,plain,
% 7.81/1.47      ( ~ v5_relat_1(X0,X1)
% 7.81/1.47      | r1_tarski(k2_relat_1(X0),X1)
% 7.81/1.47      | ~ v1_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3775,plain,
% 7.81/1.47      ( ~ v5_relat_1(sK5,sK2)
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),sK2)
% 7.81/1.47      | ~ v1_relat_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_14]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3776,plain,
% 7.81/1.47      ( v5_relat_1(sK5,sK2) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 7.81/1.47      | v1_relat_1(sK5) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_3775]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1281,plain,
% 7.81/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.81/1.47      | v1_relat_1(X1) != iProver_top
% 7.81/1.47      | v1_relat_1(X0) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4004,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) != iProver_top
% 7.81/1.47      | v1_relat_1(sK6) = iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1265,c_1281]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2019,plain,
% 7.81/1.47      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 7.81/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK4))
% 7.81/1.47      | v1_relat_1(sK6) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1557]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2020,plain,
% 7.81/1.47      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | v1_relat_1(k2_zfmisc_1(sK2,sK4)) != iProver_top
% 7.81/1.47      | v1_relat_1(sK6) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2448,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_15]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2449,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK4)) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4024,plain,
% 7.81/1.47      ( v1_relat_1(sK6) = iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_4004,c_47,c_2020,c_2449]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_20,plain,
% 7.81/1.47      ( v4_relat_1(X0,X1)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.81/1.47      inference(cnf_transformation,[],[f80]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_24,plain,
% 7.81/1.47      ( ~ v1_partfun1(X0,X1)
% 7.81/1.47      | ~ v4_relat_1(X0,X1)
% 7.81/1.47      | ~ v1_relat_1(X0)
% 7.81/1.47      | k1_relat_1(X0) = X1 ),
% 7.81/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_32,negated_conjecture,
% 7.81/1.47      ( v1_partfun1(sK6,sK2) ),
% 7.81/1.47      inference(cnf_transformation,[],[f100]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_422,plain,
% 7.81/1.47      ( ~ v4_relat_1(X0,X1)
% 7.81/1.47      | ~ v1_relat_1(X0)
% 7.81/1.47      | k1_relat_1(X0) = X1
% 7.81/1.47      | sK6 != X0
% 7.81/1.47      | sK2 != X1 ),
% 7.81/1.47      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_423,plain,
% 7.81/1.47      ( ~ v4_relat_1(sK6,sK2)
% 7.81/1.47      | ~ v1_relat_1(sK6)
% 7.81/1.47      | k1_relat_1(sK6) = sK2 ),
% 7.81/1.47      inference(unflattening,[status(thm)],[c_422]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_439,plain,
% 7.81/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ v1_relat_1(sK6)
% 7.81/1.47      | k1_relat_1(sK6) = sK2
% 7.81/1.47      | sK6 != X0
% 7.81/1.47      | sK2 != X1 ),
% 7.81/1.47      inference(resolution_lifted,[status(thm)],[c_20,c_423]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_440,plain,
% 7.81/1.47      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 7.81/1.47      | ~ v1_relat_1(sK6)
% 7.81/1.47      | k1_relat_1(sK6) = sK2 ),
% 7.81/1.47      inference(unflattening,[status(thm)],[c_439]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_668,plain,
% 7.81/1.47      ( ~ v1_relat_1(sK6) | sP0_iProver_split | k1_relat_1(sK6) = sK2 ),
% 7.81/1.47      inference(splitting,
% 7.81/1.47                [splitting(split),new_symbols(definition,[])],
% 7.81/1.47                [c_440]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1257,plain,
% 7.81/1.47      ( k1_relat_1(sK6) = sK2
% 7.81/1.47      | v1_relat_1(sK6) != iProver_top
% 7.81/1.47      | sP0_iProver_split = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4029,plain,
% 7.81/1.47      ( k1_relat_1(sK6) = sK2 | sP0_iProver_split = iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_4024,c_1257]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_667,plain,
% 7.81/1.47      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 7.81/1.47      | ~ sP0_iProver_split ),
% 7.81/1.47      inference(splitting,
% 7.81/1.47                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.81/1.47                [c_440]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1258,plain,
% 7.81/1.47      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | sP0_iProver_split != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1988,plain,
% 7.81/1.47      ( sP0_iProver_split != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1265,c_1258]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1998,plain,
% 7.81/1.47      ( ~ sP0_iProver_split ),
% 7.81/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_1988]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4860,plain,
% 7.81/1.47      ( k1_relat_1(sK6) = sK2 ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_4029,c_34,c_668,c_1998,c_2019,c_2448]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4863,plain,
% 7.81/1.47      ( k1_relset_1(sK2,sK4,sK6) = sK2 ),
% 7.81/1.47      inference(demodulation,[status(thm)],[c_4860,c_2927]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4866,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),sK2) != iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_4863,c_3590]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_5093,plain,
% 7.81/1.47      ( m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_3601,c_45,c_46,c_47,c_1595,c_2023,c_2452,c_3776,
% 7.81/1.47                 c_4866]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_5094,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.81/1.47      | sK3 = k1_xboole_0
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_5093]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_5103,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 7.81/1.47      | sK3 = k1_xboole_0 ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1266,c_5094]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_25,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 7.81/1.47      | ~ v1_funct_1(X3)
% 7.81/1.47      | ~ v1_funct_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f88]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1272,plain,
% 7.81/1.47      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 7.81/1.47      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 7.81/1.47      | v1_funct_1(X0) != iProver_top
% 7.81/1.47      | v1_funct_1(X3) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_28,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X3,X1)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | v1_xboole_0(X1)
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.81/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1269,plain,
% 7.81/1.47      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 7.81/1.47      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,X0) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.47      | v1_xboole_0(X0) = iProver_top
% 7.81/1.47      | v1_funct_1(X2) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_5788,plain,
% 7.81/1.47      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.81/1.47      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.81/1.47      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 7.81/1.47      | m1_subset_1(X5,X0) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.81/1.47      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.81/1.47      | v1_xboole_0(X0) = iProver_top
% 7.81/1.47      | v1_funct_1(X3) != iProver_top
% 7.81/1.47      | v1_funct_1(X4) != iProver_top
% 7.81/1.47      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1272,c_1269]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_27,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ v1_funct_1(X3)
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 7.81/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1270,plain,
% 7.81/1.47      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 7.81/1.47      | v1_funct_1(X0) != iProver_top
% 7.81/1.47      | v1_funct_1(X3) != iProver_top
% 7.81/1.47      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_26,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 7.81/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ v1_funct_1(X4)
% 7.81/1.47      | ~ v1_funct_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1271,plain,
% 7.81/1.47      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.47      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 7.81/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.47      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.81/1.47      | v1_funct_1(X0) != iProver_top
% 7.81/1.47      | v1_funct_1(X4) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_22821,plain,
% 7.81/1.47      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 7.81/1.47      | v1_funct_2(X3,X0,X2) != iProver_top
% 7.81/1.47      | m1_subset_1(X5,X0) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.81/1.47      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.81/1.47      | v1_xboole_0(X0) = iProver_top
% 7.81/1.47      | v1_funct_1(X4) != iProver_top
% 7.81/1.47      | v1_funct_1(X3) != iProver_top ),
% 7.81/1.47      inference(forward_subsumption_resolution,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_5788,c_1270,c_1271]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_22828,plain,
% 7.81/1.47      ( k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
% 7.81/1.47      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top
% 7.81/1.47      | v1_xboole_0(sK3) = iProver_top
% 7.81/1.47      | v1_funct_1(X1) != iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1263,c_22821]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_39,negated_conjecture,
% 7.81/1.47      ( ~ v1_xboole_0(sK3) ),
% 7.81/1.47      inference(cnf_transformation,[],[f93]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_42,plain,
% 7.81/1.47      ( v1_xboole_0(sK3) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23309,plain,
% 7.81/1.47      ( v1_funct_1(X1) != iProver_top
% 7.81/1.47      | k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_22828,c_42,c_43,c_44]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23310,plain,
% 7.81/1.47      ( k3_funct_2(sK3,X0,k8_funct_2(sK3,sK2,X0,sK5,X1),X2) = k1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,X1),X2)
% 7.81/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.81/1.47      | m1_subset_1(X2,sK3) != iProver_top
% 7.81/1.47      | v1_funct_1(X1) != iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_23309]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23321,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1265,c_23310]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1654,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | v1_funct_1(k8_funct_2(X1,X2,X3,X0,sK6))
% 7.81/1.47      | ~ v1_funct_1(sK6) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_27]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1890,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,X0,X1)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.47      | v1_funct_1(k8_funct_2(X0,X1,X2,sK5,sK6))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1654]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2472,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | v1_funct_1(k8_funct_2(sK3,sK2,X0,sK5,sK6))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1890]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3905,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_2472]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3906,plain,
% 7.81/1.47      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6)) = iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_3905]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1674,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | m1_subset_1(k8_funct_2(X1,X2,X3,X0,sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | ~ v1_funct_1(sK6) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_25]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1950,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,X0,X1)
% 7.81/1.47      | m1_subset_1(k8_funct_2(X0,X1,X2,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1674]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2491,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | m1_subset_1(k8_funct_2(sK3,sK2,X0,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1950]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3945,plain,
% 7.81/1.47      ( ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_2491]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3946,plain,
% 7.81/1.47      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top
% 7.81/1.47      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_3945]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1684,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,sK6),X1,X3)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.47      | ~ v1_funct_1(X0)
% 7.81/1.47      | ~ v1_funct_1(sK6) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_26]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1970,plain,
% 7.81/1.47      ( v1_funct_2(k8_funct_2(X0,X1,X2,sK5,sK6),X0,X2)
% 7.81/1.47      | ~ v1_funct_2(sK5,X0,X1)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1684]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2521,plain,
% 7.81/1.47      ( v1_funct_2(k8_funct_2(sK3,sK2,X0,sK5,sK6),sK3,X0)
% 7.81/1.47      | ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1970]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3948,plain,
% 7.81/1.47      ( v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4)
% 7.81/1.47      | ~ v1_funct_2(sK5,sK3,sK2)
% 7.81/1.47      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_funct_1(sK6)
% 7.81/1.47      | ~ v1_funct_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_2521]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3949,plain,
% 7.81/1.47      ( v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4) = iProver_top
% 7.81/1.47      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | v1_funct_1(sK6) != iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_3948]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_7123,plain,
% 7.81/1.47      ( ~ v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0,X1)
% 7.81/1.47      | ~ m1_subset_1(X2,X0)
% 7.81/1.47      | ~ m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.47      | v1_xboole_0(X0)
% 7.81/1.47      | ~ v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
% 7.81/1.47      | k3_funct_2(X0,X1,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X2) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X2) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_28]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_15955,plain,
% 7.81/1.47      ( ~ v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4)
% 7.81/1.47      | ~ m1_subset_1(X0,sK3)
% 7.81/1.47      | ~ m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.81/1.47      | v1_xboole_0(sK3)
% 7.81/1.47      | ~ v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6))
% 7.81/1.47      | k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_7123]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_15956,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
% 7.81/1.47      | v1_funct_2(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK3,sK4) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.81/1.47      | v1_xboole_0(sK3) = iProver_top
% 7.81/1.47      | v1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6)) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_15955]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23385,plain,
% 7.81/1.47      ( m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_23321,c_42,c_43,c_44,c_45,c_46,c_47,c_3906,c_3946,
% 7.81/1.47                 c_3949,c_15956]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23386,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),X0)
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_23385]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23394,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1266,c_23386]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3789,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK2,sK5,X0) = k1_funct_1(sK5,X0)
% 7.81/1.47      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | v1_xboole_0(sK3) = iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1263,c_1269]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4132,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK2,sK5,X0) = k1_funct_1(sK5,X0)
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_3789,c_42,c_43,c_44]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4141,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK2,sK5,sK7) = k1_funct_1(sK5,sK7) ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1266,c_4132]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_31,negated_conjecture,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7)) ),
% 7.81/1.47      inference(cnf_transformation,[],[f101]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4147,plain,
% 7.81/1.47      ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.81/1.47      inference(demodulation,[status(thm)],[c_4141,c_31]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23400,plain,
% 7.81/1.47      ( k1_funct_1(k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.81/1.47      inference(demodulation,[status(thm)],[c_23394,c_4147]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23496,plain,
% 7.81/1.47      ( sK3 = k1_xboole_0 ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_5103,c_23400]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_12,plain,
% 7.81/1.47      ( ~ v5_relat_1(X0,X1)
% 7.81/1.47      | v5_relat_1(X2,X1)
% 7.81/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 7.81/1.47      | ~ v1_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1280,plain,
% 7.81/1.47      ( v5_relat_1(X0,X1) != iProver_top
% 7.81/1.47      | v5_relat_1(X2,X1) = iProver_top
% 7.81/1.47      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.81/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_5649,plain,
% 7.81/1.47      ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
% 7.81/1.47      | v5_relat_1(sK5,X0) = iProver_top
% 7.81/1.47      | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1263,c_1280]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1606,plain,
% 7.81/1.47      ( v5_relat_1(X0,X1)
% 7.81/1.47      | ~ v5_relat_1(k2_zfmisc_1(X2,X3),X1)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.47      | ~ v1_relat_1(k2_zfmisc_1(X2,X3)) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2508,plain,
% 7.81/1.47      ( ~ v5_relat_1(k2_zfmisc_1(sK3,sK2),X0)
% 7.81/1.47      | v5_relat_1(sK5,X0)
% 7.81/1.47      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.81/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_1606]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2509,plain,
% 7.81/1.47      ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
% 7.81/1.47      | v5_relat_1(sK5,X0) = iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2508]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_6056,plain,
% 7.81/1.47      ( v5_relat_1(sK5,X0) = iProver_top
% 7.81/1.47      | v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_5649,c_45,c_2452,c_2509]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_6057,plain,
% 7.81/1.47      ( v5_relat_1(k2_zfmisc_1(sK3,sK2),X0) != iProver_top
% 7.81/1.47      | v5_relat_1(sK5,X0) = iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_6056]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23610,plain,
% 7.81/1.47      ( v5_relat_1(k2_zfmisc_1(k1_xboole_0,sK2),X0) != iProver_top
% 7.81/1.47      | v5_relat_1(sK5,X0) = iProver_top ),
% 7.81/1.47      inference(demodulation,[status(thm)],[c_23496,c_6057]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_8,plain,
% 7.81/1.47      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.81/1.47      inference(cnf_transformation,[],[f105]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_23670,plain,
% 7.81/1.47      ( v5_relat_1(sK5,X0) = iProver_top
% 7.81/1.47      | v5_relat_1(k1_xboole_0,X0) != iProver_top ),
% 7.81/1.47      inference(demodulation,[status(thm)],[c_23610,c_8]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_25158,plain,
% 7.81/1.47      ( v5_relat_1(sK5,k1_xboole_0) = iProver_top
% 7.81/1.47      | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_23670]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_14126,plain,
% 7.81/1.47      ( ~ v5_relat_1(sK5,X0)
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),X0)
% 7.81/1.47      | ~ v1_relat_1(sK5) ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_14]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_14132,plain,
% 7.81/1.47      ( v5_relat_1(sK5,X0) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 7.81/1.47      | v1_relat_1(sK5) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_14126]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_14134,plain,
% 7.81/1.47      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
% 7.81/1.47      | v1_relat_1(sK5) != iProver_top ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_14132]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_6,plain,
% 7.81/1.47      ( r1_tarski(k1_xboole_0,X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1283,plain,
% 7.81/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_30,plain,
% 7.81/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.47      | ~ m1_subset_1(X3,X1)
% 7.81/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.47      | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
% 7.81/1.47      | v1_xboole_0(X1)
% 7.81/1.47      | v1_xboole_0(X2)
% 7.81/1.47      | ~ v1_funct_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f91]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1267,plain,
% 7.81/1.47      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.47      | m1_subset_1(X3,X1) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.47      | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0)) = iProver_top
% 7.81/1.47      | v1_xboole_0(X1) = iProver_top
% 7.81/1.47      | v1_xboole_0(X2) = iProver_top
% 7.81/1.47      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3161,plain,
% 7.81/1.47      ( v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.81/1.47      | r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top
% 7.81/1.47      | v1_xboole_0(sK2) = iProver_top
% 7.81/1.47      | v1_xboole_0(sK3) = iProver_top
% 7.81/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_2849,c_1267]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3420,plain,
% 7.81/1.47      ( r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top
% 7.81/1.47      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_3161,c_41,c_42,c_43,c_44,c_45]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3421,plain,
% 7.81/1.47      ( m1_subset_1(X0,sK3) != iProver_top
% 7.81/1.47      | r2_hidden(k3_funct_2(sK3,sK2,sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 7.81/1.47      inference(renaming,[status(thm)],[c_3420]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4149,plain,
% 7.81/1.47      ( m1_subset_1(sK7,sK3) != iProver_top
% 7.81/1.47      | r2_hidden(k1_funct_1(sK5,sK7),k2_relat_1(sK5)) = iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_4141,c_3421]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_48,plain,
% 7.81/1.47      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4444,plain,
% 7.81/1.47      ( r2_hidden(k1_funct_1(sK5,sK7),k2_relat_1(sK5)) = iProver_top ),
% 7.81/1.47      inference(global_propositional_subsumption,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_4149,c_48]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2,plain,
% 7.81/1.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.81/1.47      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1286,plain,
% 7.81/1.47      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.47      | r2_hidden(X0,X2) = iProver_top
% 7.81/1.47      | r1_tarski(X1,X2) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_4664,plain,
% 7.81/1.47      ( r2_hidden(k1_funct_1(sK5,sK7),X0) = iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_4444,c_1286]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_18,plain,
% 7.81/1.47      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1276,plain,
% 7.81/1.47      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_6193,plain,
% 7.81/1.47      ( r1_tarski(X0,k1_funct_1(sK5,sK7)) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_4664,c_1276]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_11446,plain,
% 7.81/1.47      ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_1283,c_6193]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_672,plain,
% 7.81/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.47      theory(equality) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3695,plain,
% 7.81/1.47      ( ~ r1_tarski(X0,X1)
% 7.81/1.47      | r1_tarski(k2_relat_1(X2),X3)
% 7.81/1.47      | X3 != X1
% 7.81/1.47      | k2_relat_1(X2) != X0 ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_672]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3696,plain,
% 7.81/1.47      ( X0 != X1
% 7.81/1.47      | k2_relat_1(X2) != X3
% 7.81/1.47      | r1_tarski(X3,X1) != iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(X2),X0) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_3695]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_3698,plain,
% 7.81/1.47      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 7.81/1.47      | k1_xboole_0 != k1_xboole_0
% 7.81/1.47      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.81/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_3696]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_7,plain,
% 7.81/1.47      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.47      inference(cnf_transformation,[],[f104]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_1277,plain,
% 7.81/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_2230,plain,
% 7.81/1.47      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.81/1.47      inference(superposition,[status(thm)],[c_7,c_1277]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_105,plain,
% 7.81/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_107,plain,
% 7.81/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_105]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_104,plain,
% 7.81/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_9,plain,
% 7.81/1.47      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.81/1.47      | k1_xboole_0 = X1
% 7.81/1.47      | k1_xboole_0 = X0 ),
% 7.81/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_103,plain,
% 7.81/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.81/1.47      | k1_xboole_0 = k1_xboole_0 ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_9]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_13,plain,
% 7.81/1.47      ( v5_relat_1(X0,X1)
% 7.81/1.47      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.81/1.47      | ~ v1_relat_1(X0) ),
% 7.81/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_95,plain,
% 7.81/1.47      ( v5_relat_1(X0,X1) = iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.81/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.81/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_97,plain,
% 7.81/1.47      ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 7.81/1.47      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.81/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.81/1.47      inference(instantiation,[status(thm)],[c_95]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(c_16,plain,
% 7.81/1.47      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.47      inference(cnf_transformation,[],[f78]) ).
% 7.81/1.47  
% 7.81/1.47  cnf(contradiction,plain,
% 7.81/1.47      ( $false ),
% 7.81/1.47      inference(minisat,
% 7.81/1.47                [status(thm)],
% 7.81/1.47                [c_25158,c_14134,c_11446,c_3698,c_2452,c_2230,c_2023,
% 7.81/1.47                 c_107,c_104,c_103,c_97,c_16,c_45]) ).
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.47  
% 7.81/1.47  ------                               Statistics
% 7.81/1.47  
% 7.81/1.47  ------ General
% 7.81/1.47  
% 7.81/1.47  abstr_ref_over_cycles:                  0
% 7.81/1.47  abstr_ref_under_cycles:                 0
% 7.81/1.47  gc_basic_clause_elim:                   0
% 7.81/1.47  forced_gc_time:                         0
% 7.81/1.47  parsing_time:                           0.012
% 7.81/1.47  unif_index_cands_time:                  0.
% 7.81/1.47  unif_index_add_time:                    0.
% 7.81/1.47  orderings_time:                         0.
% 7.81/1.47  out_proof_time:                         0.018
% 7.81/1.47  total_time:                             0.832
% 7.81/1.47  num_of_symbols:                         60
% 7.81/1.47  num_of_terms:                           25373
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing
% 7.81/1.47  
% 7.81/1.47  num_of_splits:                          1
% 7.81/1.47  num_of_split_atoms:                     1
% 7.81/1.47  num_of_reused_defs:                     0
% 7.81/1.47  num_eq_ax_congr_red:                    34
% 7.81/1.47  num_of_sem_filtered_clauses:            1
% 7.81/1.47  num_of_subtypes:                        0
% 7.81/1.47  monotx_restored_types:                  0
% 7.81/1.47  sat_num_of_epr_types:                   0
% 7.81/1.47  sat_num_of_non_cyclic_types:            0
% 7.81/1.47  sat_guarded_non_collapsed_types:        0
% 7.81/1.47  num_pure_diseq_elim:                    0
% 7.81/1.47  simp_replaced_by:                       0
% 7.81/1.47  res_preprocessed:                       186
% 7.81/1.47  prep_upred:                             0
% 7.81/1.47  prep_unflattend:                        8
% 7.81/1.47  smt_new_axioms:                         0
% 7.81/1.47  pred_elim_cands:                        8
% 7.81/1.47  pred_elim:                              2
% 7.81/1.47  pred_elim_cl:                           3
% 7.81/1.47  pred_elim_cycles:                       5
% 7.81/1.47  merged_defs:                            0
% 7.81/1.47  merged_defs_ncl:                        0
% 7.81/1.47  bin_hyper_res:                          0
% 7.81/1.47  prep_cycles:                            4
% 7.81/1.47  pred_elim_time:                         0.002
% 7.81/1.47  splitting_time:                         0.
% 7.81/1.47  sem_filter_time:                        0.
% 7.81/1.47  monotx_time:                            0.
% 7.81/1.47  subtype_inf_time:                       0.
% 7.81/1.47  
% 7.81/1.47  ------ Problem properties
% 7.81/1.47  
% 7.81/1.47  clauses:                                38
% 7.81/1.47  conjectures:                            9
% 7.81/1.47  epr:                                    11
% 7.81/1.47  horn:                                   32
% 7.81/1.47  ground:                                 12
% 7.81/1.47  unary:                                  17
% 7.81/1.47  binary:                                 7
% 7.81/1.47  lits:                                   97
% 7.81/1.47  lits_eq:                                15
% 7.81/1.47  fd_pure:                                0
% 7.81/1.47  fd_pseudo:                              0
% 7.81/1.47  fd_cond:                                2
% 7.81/1.47  fd_pseudo_cond:                         1
% 7.81/1.47  ac_symbols:                             0
% 7.81/1.47  
% 7.81/1.47  ------ Propositional Solver
% 7.81/1.47  
% 7.81/1.47  prop_solver_calls:                      29
% 7.81/1.47  prop_fast_solver_calls:                 2995
% 7.81/1.47  smt_solver_calls:                       0
% 7.81/1.47  smt_fast_solver_calls:                  0
% 7.81/1.47  prop_num_of_clauses:                    9121
% 7.81/1.47  prop_preprocess_simplified:             18007
% 7.81/1.47  prop_fo_subsumed:                       111
% 7.81/1.47  prop_solver_time:                       0.
% 7.81/1.47  smt_solver_time:                        0.
% 7.81/1.47  smt_fast_solver_time:                   0.
% 7.81/1.47  prop_fast_solver_time:                  0.
% 7.81/1.47  prop_unsat_core_time:                   0.001
% 7.81/1.47  
% 7.81/1.47  ------ QBF
% 7.81/1.47  
% 7.81/1.47  qbf_q_res:                              0
% 7.81/1.47  qbf_num_tautologies:                    0
% 7.81/1.47  qbf_prep_cycles:                        0
% 7.81/1.47  
% 7.81/1.47  ------ BMC1
% 7.81/1.47  
% 7.81/1.47  bmc1_current_bound:                     -1
% 7.81/1.47  bmc1_last_solved_bound:                 -1
% 7.81/1.47  bmc1_unsat_core_size:                   -1
% 7.81/1.47  bmc1_unsat_core_parents_size:           -1
% 7.81/1.47  bmc1_merge_next_fun:                    0
% 7.81/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.47  
% 7.81/1.47  ------ Instantiation
% 7.81/1.47  
% 7.81/1.47  inst_num_of_clauses:                    2839
% 7.81/1.47  inst_num_in_passive:                    602
% 7.81/1.47  inst_num_in_active:                     1194
% 7.81/1.47  inst_num_in_unprocessed:                1043
% 7.81/1.47  inst_num_of_loops:                      1350
% 7.81/1.47  inst_num_of_learning_restarts:          0
% 7.81/1.47  inst_num_moves_active_passive:          154
% 7.81/1.47  inst_lit_activity:                      0
% 7.81/1.47  inst_lit_activity_moves:                0
% 7.81/1.47  inst_num_tautologies:                   0
% 7.81/1.47  inst_num_prop_implied:                  0
% 7.81/1.47  inst_num_existing_simplified:           0
% 7.81/1.47  inst_num_eq_res_simplified:             0
% 7.81/1.47  inst_num_child_elim:                    0
% 7.81/1.47  inst_num_of_dismatching_blockings:      755
% 7.81/1.47  inst_num_of_non_proper_insts:           2327
% 7.81/1.47  inst_num_of_duplicates:                 0
% 7.81/1.47  inst_inst_num_from_inst_to_res:         0
% 7.81/1.47  inst_dismatching_checking_time:         0.
% 7.81/1.47  
% 7.81/1.47  ------ Resolution
% 7.81/1.47  
% 7.81/1.47  res_num_of_clauses:                     0
% 7.81/1.47  res_num_in_passive:                     0
% 7.81/1.47  res_num_in_active:                      0
% 7.81/1.47  res_num_of_loops:                       190
% 7.81/1.47  res_forward_subset_subsumed:            133
% 7.81/1.47  res_backward_subset_subsumed:           0
% 7.81/1.47  res_forward_subsumed:                   0
% 7.81/1.47  res_backward_subsumed:                  0
% 7.81/1.47  res_forward_subsumption_resolution:     0
% 7.81/1.47  res_backward_subsumption_resolution:    0
% 7.81/1.47  res_clause_to_clause_subsumption:       5575
% 7.81/1.47  res_orphan_elimination:                 0
% 7.81/1.47  res_tautology_del:                      48
% 7.81/1.47  res_num_eq_res_simplified:              0
% 7.81/1.47  res_num_sel_changes:                    0
% 7.81/1.47  res_moves_from_active_to_pass:          0
% 7.81/1.47  
% 7.81/1.47  ------ Superposition
% 7.81/1.47  
% 7.81/1.47  sup_time_total:                         0.
% 7.81/1.47  sup_time_generating:                    0.
% 7.81/1.47  sup_time_sim_full:                      0.
% 7.81/1.47  sup_time_sim_immed:                     0.
% 7.81/1.47  
% 7.81/1.47  sup_num_of_clauses:                     381
% 7.81/1.47  sup_num_in_active:                      126
% 7.81/1.47  sup_num_in_passive:                     255
% 7.81/1.47  sup_num_of_loops:                       269
% 7.81/1.47  sup_fw_superposition:                   370
% 7.81/1.47  sup_bw_superposition:                   74
% 7.81/1.47  sup_immediate_simplified:               141
% 7.81/1.47  sup_given_eliminated:                   1
% 7.81/1.47  comparisons_done:                       0
% 7.81/1.47  comparisons_avoided:                    41
% 7.81/1.47  
% 7.81/1.47  ------ Simplifications
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  sim_fw_subset_subsumed:                 13
% 7.81/1.47  sim_bw_subset_subsumed:                 31
% 7.81/1.47  sim_fw_subsumed:                        24
% 7.81/1.47  sim_bw_subsumed:                        2
% 7.81/1.47  sim_fw_subsumption_res:                 27
% 7.81/1.47  sim_bw_subsumption_res:                 0
% 7.81/1.47  sim_tautology_del:                      1
% 7.81/1.47  sim_eq_tautology_del:                   15
% 7.81/1.47  sim_eq_res_simp:                        0
% 7.81/1.47  sim_fw_demodulated:                     40
% 7.81/1.47  sim_bw_demodulated:                     131
% 7.81/1.47  sim_light_normalised:                   52
% 7.81/1.47  sim_joinable_taut:                      0
% 7.81/1.47  sim_joinable_simp:                      0
% 7.81/1.47  sim_ac_normalised:                      0
% 7.81/1.47  sim_smt_subsumption:                    0
% 7.81/1.47  
%------------------------------------------------------------------------------
