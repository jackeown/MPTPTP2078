%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:20 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 495 expanded)
%              Number of clauses        :   91 ( 130 expanded)
%              Number of leaves         :   20 ( 183 expanded)
%              Depth                    :   22
%              Number of atoms          :  604 (3953 expanded)
%              Number of equality atoms :  235 ( 669 expanded)
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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f36,f35,f34,f33,f32])).

fof(f59,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1182,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1181,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1179,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1186,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1183,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2473,plain,
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
    inference(superposition,[status(thm)],[c_1186,c_1183])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1184,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1185,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4306,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2473,c_1184,c_1185])).

cnf(c_4313,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_4306])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5120,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4313,c_25,c_26,c_27])).

cnf(c_5132,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_5120])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5173,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5132,c_29])).

cnf(c_5174,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5173])).

cnf(c_5181,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1182,c_5174])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1187,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1748,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1181,c_1187])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_329,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X2)
    | k1_relset_1(X2,X7,X6) != X5
    | k2_relset_1(X1,X2,X0) != X4
    | k1_funct_1(k8_funct_2(X1,X2,X7,X0,X6),X3) = k1_funct_1(X6,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_330,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(k1_relset_1(X2,X5,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_1172,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_relset_1(X0,X1,X3),k1_zfmisc_1(k1_relset_1(X1,X2,X4))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_1755,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1172])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1909,plain,
    ( m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1755,c_24,c_29,c_30])).

cnf(c_1910,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1909])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_293,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_294,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_294])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_791,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_311])).

cnf(c_1173,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_820,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1640,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1641,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1765,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1766,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_790,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_311])).

cnf(c_1174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1779,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1174])).

cnf(c_1814,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1173,c_30,c_820,c_1641,c_1766,c_1779])).

cnf(c_1915,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1910,c_1814])).

cnf(c_2060,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1915])).

cnf(c_2436,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_2060])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_376,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_2860,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_26,c_27,c_376])).

cnf(c_2861,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2860])).

cnf(c_2868,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1182,c_2861])).

cnf(c_5182,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_5181,c_2868])).

cnf(c_794,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1381,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != X0
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1491,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(X0,X1)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_2402,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_805,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_1492,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != X0
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1740,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != X0
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,X0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_2196,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_1430,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1549,plain,
    ( ~ v1_funct_2(sK3,sK1,X0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,X0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_1551,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_793,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1504,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_14,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5182,c_2402,c_2196,c_1551,c_1504,c_14,c_16,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:14:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.72/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/0.93  
% 2.72/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.93  
% 2.72/0.93  ------  iProver source info
% 2.72/0.93  
% 2.72/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.93  git: non_committed_changes: false
% 2.72/0.93  git: last_make_outside_of_git: false
% 2.72/0.93  
% 2.72/0.93  ------ 
% 2.72/0.93  
% 2.72/0.93  ------ Input Options
% 2.72/0.93  
% 2.72/0.93  --out_options                           all
% 2.72/0.93  --tptp_safe_out                         true
% 2.72/0.93  --problem_path                          ""
% 2.72/0.93  --include_path                          ""
% 2.72/0.93  --clausifier                            res/vclausify_rel
% 2.72/0.93  --clausifier_options                    --mode clausify
% 2.72/0.93  --stdin                                 false
% 2.72/0.93  --stats_out                             all
% 2.72/0.93  
% 2.72/0.93  ------ General Options
% 2.72/0.93  
% 2.72/0.93  --fof                                   false
% 2.72/0.93  --time_out_real                         305.
% 2.72/0.93  --time_out_virtual                      -1.
% 2.72/0.93  --symbol_type_check                     false
% 2.72/0.93  --clausify_out                          false
% 2.72/0.93  --sig_cnt_out                           false
% 2.72/0.93  --trig_cnt_out                          false
% 2.72/0.93  --trig_cnt_out_tolerance                1.
% 2.72/0.93  --trig_cnt_out_sk_spl                   false
% 2.72/0.93  --abstr_cl_out                          false
% 2.72/0.93  
% 2.72/0.93  ------ Global Options
% 2.72/0.93  
% 2.72/0.93  --schedule                              default
% 2.72/0.93  --add_important_lit                     false
% 2.72/0.93  --prop_solver_per_cl                    1000
% 2.72/0.93  --min_unsat_core                        false
% 2.72/0.93  --soft_assumptions                      false
% 2.72/0.93  --soft_lemma_size                       3
% 2.72/0.93  --prop_impl_unit_size                   0
% 2.72/0.93  --prop_impl_unit                        []
% 2.72/0.93  --share_sel_clauses                     true
% 2.72/0.93  --reset_solvers                         false
% 2.72/0.93  --bc_imp_inh                            [conj_cone]
% 2.72/0.93  --conj_cone_tolerance                   3.
% 2.72/0.93  --extra_neg_conj                        none
% 2.72/0.93  --large_theory_mode                     true
% 2.72/0.93  --prolific_symb_bound                   200
% 2.72/0.93  --lt_threshold                          2000
% 2.72/0.93  --clause_weak_htbl                      true
% 2.72/0.93  --gc_record_bc_elim                     false
% 2.72/0.93  
% 2.72/0.93  ------ Preprocessing Options
% 2.72/0.93  
% 2.72/0.93  --preprocessing_flag                    true
% 2.72/0.93  --time_out_prep_mult                    0.1
% 2.72/0.93  --splitting_mode                        input
% 2.72/0.93  --splitting_grd                         true
% 2.72/0.93  --splitting_cvd                         false
% 2.72/0.93  --splitting_cvd_svl                     false
% 2.72/0.93  --splitting_nvd                         32
% 2.72/0.93  --sub_typing                            true
% 2.72/0.93  --prep_gs_sim                           true
% 2.72/0.93  --prep_unflatten                        true
% 2.72/0.93  --prep_res_sim                          true
% 2.72/0.93  --prep_upred                            true
% 2.72/0.93  --prep_sem_filter                       exhaustive
% 2.72/0.93  --prep_sem_filter_out                   false
% 2.72/0.93  --pred_elim                             true
% 2.72/0.93  --res_sim_input                         true
% 2.72/0.93  --eq_ax_congr_red                       true
% 2.72/0.93  --pure_diseq_elim                       true
% 2.72/0.93  --brand_transform                       false
% 2.72/0.93  --non_eq_to_eq                          false
% 2.72/0.93  --prep_def_merge                        true
% 2.72/0.93  --prep_def_merge_prop_impl              false
% 2.72/0.93  --prep_def_merge_mbd                    true
% 2.72/0.93  --prep_def_merge_tr_red                 false
% 2.72/0.93  --prep_def_merge_tr_cl                  false
% 2.72/0.93  --smt_preprocessing                     true
% 2.72/0.93  --smt_ac_axioms                         fast
% 2.72/0.93  --preprocessed_out                      false
% 2.72/0.93  --preprocessed_stats                    false
% 2.72/0.93  
% 2.72/0.93  ------ Abstraction refinement Options
% 2.72/0.93  
% 2.72/0.93  --abstr_ref                             []
% 2.72/0.93  --abstr_ref_prep                        false
% 2.72/0.93  --abstr_ref_until_sat                   false
% 2.72/0.93  --abstr_ref_sig_restrict                funpre
% 2.72/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.93  --abstr_ref_under                       []
% 2.72/0.93  
% 2.72/0.93  ------ SAT Options
% 2.72/0.93  
% 2.72/0.93  --sat_mode                              false
% 2.72/0.93  --sat_fm_restart_options                ""
% 2.72/0.93  --sat_gr_def                            false
% 2.72/0.93  --sat_epr_types                         true
% 2.72/0.93  --sat_non_cyclic_types                  false
% 2.72/0.93  --sat_finite_models                     false
% 2.72/0.93  --sat_fm_lemmas                         false
% 2.72/0.93  --sat_fm_prep                           false
% 2.72/0.93  --sat_fm_uc_incr                        true
% 2.72/0.93  --sat_out_model                         small
% 2.72/0.93  --sat_out_clauses                       false
% 2.72/0.93  
% 2.72/0.93  ------ QBF Options
% 2.72/0.93  
% 2.72/0.93  --qbf_mode                              false
% 2.72/0.93  --qbf_elim_univ                         false
% 2.72/0.93  --qbf_dom_inst                          none
% 2.72/0.93  --qbf_dom_pre_inst                      false
% 2.72/0.93  --qbf_sk_in                             false
% 2.72/0.93  --qbf_pred_elim                         true
% 2.72/0.93  --qbf_split                             512
% 2.72/0.93  
% 2.72/0.93  ------ BMC1 Options
% 2.72/0.93  
% 2.72/0.93  --bmc1_incremental                      false
% 2.72/0.93  --bmc1_axioms                           reachable_all
% 2.72/0.93  --bmc1_min_bound                        0
% 2.72/0.93  --bmc1_max_bound                        -1
% 2.72/0.93  --bmc1_max_bound_default                -1
% 2.72/0.93  --bmc1_symbol_reachability              true
% 2.72/0.93  --bmc1_property_lemmas                  false
% 2.72/0.93  --bmc1_k_induction                      false
% 2.72/0.93  --bmc1_non_equiv_states                 false
% 2.72/0.93  --bmc1_deadlock                         false
% 2.72/0.93  --bmc1_ucm                              false
% 2.72/0.93  --bmc1_add_unsat_core                   none
% 2.72/0.93  --bmc1_unsat_core_children              false
% 2.72/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.93  --bmc1_out_stat                         full
% 2.72/0.93  --bmc1_ground_init                      false
% 2.72/0.93  --bmc1_pre_inst_next_state              false
% 2.72/0.93  --bmc1_pre_inst_state                   false
% 2.72/0.93  --bmc1_pre_inst_reach_state             false
% 2.72/0.93  --bmc1_out_unsat_core                   false
% 2.72/0.93  --bmc1_aig_witness_out                  false
% 2.72/0.93  --bmc1_verbose                          false
% 2.72/0.93  --bmc1_dump_clauses_tptp                false
% 2.72/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.93  --bmc1_dump_file                        -
% 2.72/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.93  --bmc1_ucm_extend_mode                  1
% 2.72/0.93  --bmc1_ucm_init_mode                    2
% 2.72/0.93  --bmc1_ucm_cone_mode                    none
% 2.72/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.93  --bmc1_ucm_relax_model                  4
% 2.72/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.93  --bmc1_ucm_layered_model                none
% 2.72/0.93  --bmc1_ucm_max_lemma_size               10
% 2.72/0.93  
% 2.72/0.93  ------ AIG Options
% 2.72/0.93  
% 2.72/0.93  --aig_mode                              false
% 2.72/0.93  
% 2.72/0.93  ------ Instantiation Options
% 2.72/0.93  
% 2.72/0.93  --instantiation_flag                    true
% 2.72/0.93  --inst_sos_flag                         false
% 2.72/0.93  --inst_sos_phase                        true
% 2.72/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.93  --inst_lit_sel_side                     num_symb
% 2.72/0.93  --inst_solver_per_active                1400
% 2.72/0.93  --inst_solver_calls_frac                1.
% 2.72/0.93  --inst_passive_queue_type               priority_queues
% 2.72/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.93  --inst_passive_queues_freq              [25;2]
% 2.72/0.93  --inst_dismatching                      true
% 2.72/0.93  --inst_eager_unprocessed_to_passive     true
% 2.72/0.93  --inst_prop_sim_given                   true
% 2.72/0.93  --inst_prop_sim_new                     false
% 2.72/0.93  --inst_subs_new                         false
% 2.72/0.93  --inst_eq_res_simp                      false
% 2.72/0.93  --inst_subs_given                       false
% 2.72/0.93  --inst_orphan_elimination               true
% 2.72/0.93  --inst_learning_loop_flag               true
% 2.72/0.93  --inst_learning_start                   3000
% 2.72/0.93  --inst_learning_factor                  2
% 2.72/0.93  --inst_start_prop_sim_after_learn       3
% 2.72/0.93  --inst_sel_renew                        solver
% 2.72/0.93  --inst_lit_activity_flag                true
% 2.72/0.93  --inst_restr_to_given                   false
% 2.72/0.93  --inst_activity_threshold               500
% 2.72/0.93  --inst_out_proof                        true
% 2.72/0.93  
% 2.72/0.93  ------ Resolution Options
% 2.72/0.93  
% 2.72/0.93  --resolution_flag                       true
% 2.72/0.93  --res_lit_sel                           adaptive
% 2.72/0.93  --res_lit_sel_side                      none
% 2.72/0.93  --res_ordering                          kbo
% 2.72/0.93  --res_to_prop_solver                    active
% 2.72/0.93  --res_prop_simpl_new                    false
% 2.72/0.93  --res_prop_simpl_given                  true
% 2.72/0.93  --res_passive_queue_type                priority_queues
% 2.72/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.93  --res_passive_queues_freq               [15;5]
% 2.72/0.93  --res_forward_subs                      full
% 2.72/0.93  --res_backward_subs                     full
% 2.72/0.93  --res_forward_subs_resolution           true
% 2.72/0.93  --res_backward_subs_resolution          true
% 2.72/0.93  --res_orphan_elimination                true
% 2.72/0.93  --res_time_limit                        2.
% 2.72/0.93  --res_out_proof                         true
% 2.72/0.93  
% 2.72/0.93  ------ Superposition Options
% 2.72/0.93  
% 2.72/0.93  --superposition_flag                    true
% 2.72/0.93  --sup_passive_queue_type                priority_queues
% 2.72/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.93  --demod_completeness_check              fast
% 2.72/0.93  --demod_use_ground                      true
% 2.72/0.93  --sup_to_prop_solver                    passive
% 2.72/0.93  --sup_prop_simpl_new                    true
% 2.72/0.93  --sup_prop_simpl_given                  true
% 2.72/0.93  --sup_fun_splitting                     false
% 2.72/0.93  --sup_smt_interval                      50000
% 2.72/0.93  
% 2.72/0.93  ------ Superposition Simplification Setup
% 2.72/0.93  
% 2.72/0.93  --sup_indices_passive                   []
% 2.72/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.93  --sup_full_bw                           [BwDemod]
% 2.72/0.93  --sup_immed_triv                        [TrivRules]
% 2.72/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.93  --sup_immed_bw_main                     []
% 2.72/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.94  
% 2.72/0.94  ------ Combination Options
% 2.72/0.94  
% 2.72/0.94  --comb_res_mult                         3
% 2.72/0.94  --comb_sup_mult                         2
% 2.72/0.94  --comb_inst_mult                        10
% 2.72/0.94  
% 2.72/0.94  ------ Debug Options
% 2.72/0.94  
% 2.72/0.94  --dbg_backtrace                         false
% 2.72/0.94  --dbg_dump_prop_clauses                 false
% 2.72/0.94  --dbg_dump_prop_clauses_file            -
% 2.72/0.94  --dbg_out_stat                          false
% 2.72/0.94  ------ Parsing...
% 2.72/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.94  
% 2.72/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.72/0.94  
% 2.72/0.94  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.94  
% 2.72/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.94  ------ Proving...
% 2.72/0.94  ------ Problem Properties 
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  clauses                                 21
% 2.72/0.94  conjectures                             9
% 2.72/0.94  EPR                                     7
% 2.72/0.94  Horn                                    18
% 2.72/0.94  unary                                   11
% 2.72/0.94  binary                                  3
% 2.72/0.94  lits                                    57
% 2.72/0.94  lits eq                                 6
% 2.72/0.94  fd_pure                                 0
% 2.72/0.94  fd_pseudo                               0
% 2.72/0.94  fd_cond                                 1
% 2.72/0.94  fd_pseudo_cond                          0
% 2.72/0.94  AC symbols                              0
% 2.72/0.94  
% 2.72/0.94  ------ Schedule dynamic 5 is on 
% 2.72/0.94  
% 2.72/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  ------ 
% 2.72/0.94  Current options:
% 2.72/0.94  ------ 
% 2.72/0.94  
% 2.72/0.94  ------ Input Options
% 2.72/0.94  
% 2.72/0.94  --out_options                           all
% 2.72/0.94  --tptp_safe_out                         true
% 2.72/0.94  --problem_path                          ""
% 2.72/0.94  --include_path                          ""
% 2.72/0.94  --clausifier                            res/vclausify_rel
% 2.72/0.94  --clausifier_options                    --mode clausify
% 2.72/0.94  --stdin                                 false
% 2.72/0.94  --stats_out                             all
% 2.72/0.94  
% 2.72/0.94  ------ General Options
% 2.72/0.94  
% 2.72/0.94  --fof                                   false
% 2.72/0.94  --time_out_real                         305.
% 2.72/0.94  --time_out_virtual                      -1.
% 2.72/0.94  --symbol_type_check                     false
% 2.72/0.94  --clausify_out                          false
% 2.72/0.94  --sig_cnt_out                           false
% 2.72/0.94  --trig_cnt_out                          false
% 2.72/0.94  --trig_cnt_out_tolerance                1.
% 2.72/0.94  --trig_cnt_out_sk_spl                   false
% 2.72/0.94  --abstr_cl_out                          false
% 2.72/0.94  
% 2.72/0.94  ------ Global Options
% 2.72/0.94  
% 2.72/0.94  --schedule                              default
% 2.72/0.94  --add_important_lit                     false
% 2.72/0.94  --prop_solver_per_cl                    1000
% 2.72/0.94  --min_unsat_core                        false
% 2.72/0.94  --soft_assumptions                      false
% 2.72/0.94  --soft_lemma_size                       3
% 2.72/0.94  --prop_impl_unit_size                   0
% 2.72/0.94  --prop_impl_unit                        []
% 2.72/0.94  --share_sel_clauses                     true
% 2.72/0.94  --reset_solvers                         false
% 2.72/0.94  --bc_imp_inh                            [conj_cone]
% 2.72/0.94  --conj_cone_tolerance                   3.
% 2.72/0.94  --extra_neg_conj                        none
% 2.72/0.94  --large_theory_mode                     true
% 2.72/0.94  --prolific_symb_bound                   200
% 2.72/0.94  --lt_threshold                          2000
% 2.72/0.94  --clause_weak_htbl                      true
% 2.72/0.94  --gc_record_bc_elim                     false
% 2.72/0.94  
% 2.72/0.94  ------ Preprocessing Options
% 2.72/0.94  
% 2.72/0.94  --preprocessing_flag                    true
% 2.72/0.94  --time_out_prep_mult                    0.1
% 2.72/0.94  --splitting_mode                        input
% 2.72/0.94  --splitting_grd                         true
% 2.72/0.94  --splitting_cvd                         false
% 2.72/0.94  --splitting_cvd_svl                     false
% 2.72/0.94  --splitting_nvd                         32
% 2.72/0.94  --sub_typing                            true
% 2.72/0.94  --prep_gs_sim                           true
% 2.72/0.94  --prep_unflatten                        true
% 2.72/0.94  --prep_res_sim                          true
% 2.72/0.94  --prep_upred                            true
% 2.72/0.94  --prep_sem_filter                       exhaustive
% 2.72/0.94  --prep_sem_filter_out                   false
% 2.72/0.94  --pred_elim                             true
% 2.72/0.94  --res_sim_input                         true
% 2.72/0.94  --eq_ax_congr_red                       true
% 2.72/0.94  --pure_diseq_elim                       true
% 2.72/0.94  --brand_transform                       false
% 2.72/0.94  --non_eq_to_eq                          false
% 2.72/0.94  --prep_def_merge                        true
% 2.72/0.94  --prep_def_merge_prop_impl              false
% 2.72/0.94  --prep_def_merge_mbd                    true
% 2.72/0.94  --prep_def_merge_tr_red                 false
% 2.72/0.94  --prep_def_merge_tr_cl                  false
% 2.72/0.94  --smt_preprocessing                     true
% 2.72/0.94  --smt_ac_axioms                         fast
% 2.72/0.94  --preprocessed_out                      false
% 2.72/0.94  --preprocessed_stats                    false
% 2.72/0.94  
% 2.72/0.94  ------ Abstraction refinement Options
% 2.72/0.94  
% 2.72/0.94  --abstr_ref                             []
% 2.72/0.94  --abstr_ref_prep                        false
% 2.72/0.94  --abstr_ref_until_sat                   false
% 2.72/0.94  --abstr_ref_sig_restrict                funpre
% 2.72/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.94  --abstr_ref_under                       []
% 2.72/0.94  
% 2.72/0.94  ------ SAT Options
% 2.72/0.94  
% 2.72/0.94  --sat_mode                              false
% 2.72/0.94  --sat_fm_restart_options                ""
% 2.72/0.94  --sat_gr_def                            false
% 2.72/0.94  --sat_epr_types                         true
% 2.72/0.94  --sat_non_cyclic_types                  false
% 2.72/0.94  --sat_finite_models                     false
% 2.72/0.94  --sat_fm_lemmas                         false
% 2.72/0.94  --sat_fm_prep                           false
% 2.72/0.94  --sat_fm_uc_incr                        true
% 2.72/0.94  --sat_out_model                         small
% 2.72/0.94  --sat_out_clauses                       false
% 2.72/0.94  
% 2.72/0.94  ------ QBF Options
% 2.72/0.94  
% 2.72/0.94  --qbf_mode                              false
% 2.72/0.94  --qbf_elim_univ                         false
% 2.72/0.94  --qbf_dom_inst                          none
% 2.72/0.94  --qbf_dom_pre_inst                      false
% 2.72/0.94  --qbf_sk_in                             false
% 2.72/0.94  --qbf_pred_elim                         true
% 2.72/0.94  --qbf_split                             512
% 2.72/0.94  
% 2.72/0.94  ------ BMC1 Options
% 2.72/0.94  
% 2.72/0.94  --bmc1_incremental                      false
% 2.72/0.94  --bmc1_axioms                           reachable_all
% 2.72/0.94  --bmc1_min_bound                        0
% 2.72/0.94  --bmc1_max_bound                        -1
% 2.72/0.94  --bmc1_max_bound_default                -1
% 2.72/0.94  --bmc1_symbol_reachability              true
% 2.72/0.94  --bmc1_property_lemmas                  false
% 2.72/0.94  --bmc1_k_induction                      false
% 2.72/0.94  --bmc1_non_equiv_states                 false
% 2.72/0.94  --bmc1_deadlock                         false
% 2.72/0.94  --bmc1_ucm                              false
% 2.72/0.94  --bmc1_add_unsat_core                   none
% 2.72/0.94  --bmc1_unsat_core_children              false
% 2.72/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.94  --bmc1_out_stat                         full
% 2.72/0.94  --bmc1_ground_init                      false
% 2.72/0.94  --bmc1_pre_inst_next_state              false
% 2.72/0.94  --bmc1_pre_inst_state                   false
% 2.72/0.94  --bmc1_pre_inst_reach_state             false
% 2.72/0.94  --bmc1_out_unsat_core                   false
% 2.72/0.94  --bmc1_aig_witness_out                  false
% 2.72/0.94  --bmc1_verbose                          false
% 2.72/0.94  --bmc1_dump_clauses_tptp                false
% 2.72/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.94  --bmc1_dump_file                        -
% 2.72/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.94  --bmc1_ucm_extend_mode                  1
% 2.72/0.94  --bmc1_ucm_init_mode                    2
% 2.72/0.94  --bmc1_ucm_cone_mode                    none
% 2.72/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.94  --bmc1_ucm_relax_model                  4
% 2.72/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.94  --bmc1_ucm_layered_model                none
% 2.72/0.94  --bmc1_ucm_max_lemma_size               10
% 2.72/0.94  
% 2.72/0.94  ------ AIG Options
% 2.72/0.94  
% 2.72/0.94  --aig_mode                              false
% 2.72/0.94  
% 2.72/0.94  ------ Instantiation Options
% 2.72/0.94  
% 2.72/0.94  --instantiation_flag                    true
% 2.72/0.94  --inst_sos_flag                         false
% 2.72/0.94  --inst_sos_phase                        true
% 2.72/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.94  --inst_lit_sel_side                     none
% 2.72/0.94  --inst_solver_per_active                1400
% 2.72/0.94  --inst_solver_calls_frac                1.
% 2.72/0.94  --inst_passive_queue_type               priority_queues
% 2.72/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.94  --inst_passive_queues_freq              [25;2]
% 2.72/0.94  --inst_dismatching                      true
% 2.72/0.94  --inst_eager_unprocessed_to_passive     true
% 2.72/0.94  --inst_prop_sim_given                   true
% 2.72/0.94  --inst_prop_sim_new                     false
% 2.72/0.94  --inst_subs_new                         false
% 2.72/0.94  --inst_eq_res_simp                      false
% 2.72/0.94  --inst_subs_given                       false
% 2.72/0.94  --inst_orphan_elimination               true
% 2.72/0.94  --inst_learning_loop_flag               true
% 2.72/0.94  --inst_learning_start                   3000
% 2.72/0.94  --inst_learning_factor                  2
% 2.72/0.94  --inst_start_prop_sim_after_learn       3
% 2.72/0.94  --inst_sel_renew                        solver
% 2.72/0.94  --inst_lit_activity_flag                true
% 2.72/0.94  --inst_restr_to_given                   false
% 2.72/0.94  --inst_activity_threshold               500
% 2.72/0.94  --inst_out_proof                        true
% 2.72/0.94  
% 2.72/0.94  ------ Resolution Options
% 2.72/0.94  
% 2.72/0.94  --resolution_flag                       false
% 2.72/0.94  --res_lit_sel                           adaptive
% 2.72/0.94  --res_lit_sel_side                      none
% 2.72/0.94  --res_ordering                          kbo
% 2.72/0.94  --res_to_prop_solver                    active
% 2.72/0.94  --res_prop_simpl_new                    false
% 2.72/0.94  --res_prop_simpl_given                  true
% 2.72/0.94  --res_passive_queue_type                priority_queues
% 2.72/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.94  --res_passive_queues_freq               [15;5]
% 2.72/0.94  --res_forward_subs                      full
% 2.72/0.94  --res_backward_subs                     full
% 2.72/0.94  --res_forward_subs_resolution           true
% 2.72/0.94  --res_backward_subs_resolution          true
% 2.72/0.94  --res_orphan_elimination                true
% 2.72/0.94  --res_time_limit                        2.
% 2.72/0.94  --res_out_proof                         true
% 2.72/0.94  
% 2.72/0.94  ------ Superposition Options
% 2.72/0.94  
% 2.72/0.94  --superposition_flag                    true
% 2.72/0.94  --sup_passive_queue_type                priority_queues
% 2.72/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.94  --demod_completeness_check              fast
% 2.72/0.94  --demod_use_ground                      true
% 2.72/0.94  --sup_to_prop_solver                    passive
% 2.72/0.94  --sup_prop_simpl_new                    true
% 2.72/0.94  --sup_prop_simpl_given                  true
% 2.72/0.94  --sup_fun_splitting                     false
% 2.72/0.94  --sup_smt_interval                      50000
% 2.72/0.94  
% 2.72/0.94  ------ Superposition Simplification Setup
% 2.72/0.94  
% 2.72/0.94  --sup_indices_passive                   []
% 2.72/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.94  --sup_full_bw                           [BwDemod]
% 2.72/0.94  --sup_immed_triv                        [TrivRules]
% 2.72/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.94  --sup_immed_bw_main                     []
% 2.72/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.94  
% 2.72/0.94  ------ Combination Options
% 2.72/0.94  
% 2.72/0.94  --comb_res_mult                         3
% 2.72/0.94  --comb_sup_mult                         2
% 2.72/0.94  --comb_inst_mult                        10
% 2.72/0.94  
% 2.72/0.94  ------ Debug Options
% 2.72/0.94  
% 2.72/0.94  --dbg_backtrace                         false
% 2.72/0.94  --dbg_dump_prop_clauses                 false
% 2.72/0.94  --dbg_dump_prop_clauses_file            -
% 2.72/0.94  --dbg_out_stat                          false
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  ------ Proving...
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  % SZS status Theorem for theBenchmark.p
% 2.72/0.94  
% 2.72/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.94  
% 2.72/0.94  fof(f12,conjecture,(
% 2.72/0.94    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f13,negated_conjecture,(
% 2.72/0.94    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.72/0.94    inference(negated_conjecture,[],[f12])).
% 2.72/0.94  
% 2.72/0.94  fof(f29,plain,(
% 2.72/0.94    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.72/0.94    inference(ennf_transformation,[],[f13])).
% 2.72/0.94  
% 2.72/0.94  fof(f30,plain,(
% 2.72/0.94    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.72/0.94    inference(flattening,[],[f29])).
% 2.72/0.94  
% 2.72/0.94  fof(f36,plain,(
% 2.72/0.94    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.72/0.94    introduced(choice_axiom,[])).
% 2.72/0.94  
% 2.72/0.94  fof(f35,plain,(
% 2.72/0.94    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.72/0.94    introduced(choice_axiom,[])).
% 2.72/0.94  
% 2.72/0.94  fof(f34,plain,(
% 2.72/0.94    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.72/0.94    introduced(choice_axiom,[])).
% 2.72/0.94  
% 2.72/0.94  fof(f33,plain,(
% 2.72/0.94    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.72/0.94    introduced(choice_axiom,[])).
% 2.72/0.94  
% 2.72/0.94  fof(f32,plain,(
% 2.72/0.94    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.72/0.94    introduced(choice_axiom,[])).
% 2.72/0.94  
% 2.72/0.94  fof(f37,plain,(
% 2.72/0.94    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.72/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f36,f35,f34,f33,f32])).
% 2.72/0.94  
% 2.72/0.94  fof(f59,plain,(
% 2.72/0.94    m1_subset_1(sK5,sK1)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f58,plain,(
% 2.72/0.94    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f56,plain,(
% 2.72/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f9,axiom,(
% 2.72/0.94    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f23,plain,(
% 2.72/0.94    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.72/0.94    inference(ennf_transformation,[],[f9])).
% 2.72/0.94  
% 2.72/0.94  fof(f24,plain,(
% 2.72/0.94    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.72/0.94    inference(flattening,[],[f23])).
% 2.72/0.94  
% 2.72/0.94  fof(f49,plain,(
% 2.72/0.94    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f24])).
% 2.72/0.94  
% 2.72/0.94  fof(f10,axiom,(
% 2.72/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f25,plain,(
% 2.72/0.94    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.72/0.94    inference(ennf_transformation,[],[f10])).
% 2.72/0.94  
% 2.72/0.94  fof(f26,plain,(
% 2.72/0.94    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.72/0.94    inference(flattening,[],[f25])).
% 2.72/0.94  
% 2.72/0.94  fof(f50,plain,(
% 2.72/0.94    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f26])).
% 2.72/0.94  
% 2.72/0.94  fof(f47,plain,(
% 2.72/0.94    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f24])).
% 2.72/0.94  
% 2.72/0.94  fof(f48,plain,(
% 2.72/0.94    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f24])).
% 2.72/0.94  
% 2.72/0.94  fof(f53,plain,(
% 2.72/0.94    ~v1_xboole_0(sK1)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f54,plain,(
% 2.72/0.94    v1_funct_1(sK3)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f55,plain,(
% 2.72/0.94    v1_funct_2(sK3,sK1,sK0)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f57,plain,(
% 2.72/0.94    v1_funct_1(sK4)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f6,axiom,(
% 2.72/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f19,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.94    inference(ennf_transformation,[],[f6])).
% 2.72/0.94  
% 2.72/0.94  fof(f43,plain,(
% 2.72/0.94    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.94    inference(cnf_transformation,[],[f19])).
% 2.72/0.94  
% 2.72/0.94  fof(f7,axiom,(
% 2.72/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f20,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.94    inference(ennf_transformation,[],[f7])).
% 2.72/0.94  
% 2.72/0.94  fof(f44,plain,(
% 2.72/0.94    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.94    inference(cnf_transformation,[],[f20])).
% 2.72/0.94  
% 2.72/0.94  fof(f2,axiom,(
% 2.72/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f14,plain,(
% 2.72/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.72/0.94    inference(unused_predicate_definition_removal,[],[f2])).
% 2.72/0.94  
% 2.72/0.94  fof(f16,plain,(
% 2.72/0.94    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.72/0.94    inference(ennf_transformation,[],[f14])).
% 2.72/0.94  
% 2.72/0.94  fof(f39,plain,(
% 2.72/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.72/0.94    inference(cnf_transformation,[],[f16])).
% 2.72/0.94  
% 2.72/0.94  fof(f11,axiom,(
% 2.72/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f27,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.72/0.94    inference(ennf_transformation,[],[f11])).
% 2.72/0.94  
% 2.72/0.94  fof(f28,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.72/0.94    inference(flattening,[],[f27])).
% 2.72/0.94  
% 2.72/0.94  fof(f51,plain,(
% 2.72/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f28])).
% 2.72/0.94  
% 2.72/0.94  fof(f52,plain,(
% 2.72/0.94    ~v1_xboole_0(sK0)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f5,axiom,(
% 2.72/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f15,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.72/0.94    inference(pure_predicate_removal,[],[f5])).
% 2.72/0.94  
% 2.72/0.94  fof(f18,plain,(
% 2.72/0.94    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.94    inference(ennf_transformation,[],[f15])).
% 2.72/0.94  
% 2.72/0.94  fof(f42,plain,(
% 2.72/0.94    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.94    inference(cnf_transformation,[],[f18])).
% 2.72/0.94  
% 2.72/0.94  fof(f8,axiom,(
% 2.72/0.94    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f21,plain,(
% 2.72/0.94    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.72/0.94    inference(ennf_transformation,[],[f8])).
% 2.72/0.94  
% 2.72/0.94  fof(f22,plain,(
% 2.72/0.94    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.72/0.94    inference(flattening,[],[f21])).
% 2.72/0.94  
% 2.72/0.94  fof(f31,plain,(
% 2.72/0.94    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.72/0.94    inference(nnf_transformation,[],[f22])).
% 2.72/0.94  
% 2.72/0.94  fof(f45,plain,(
% 2.72/0.94    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f31])).
% 2.72/0.94  
% 2.72/0.94  fof(f60,plain,(
% 2.72/0.94    v1_partfun1(sK4,sK0)),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  fof(f3,axiom,(
% 2.72/0.94    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f17,plain,(
% 2.72/0.94    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.72/0.94    inference(ennf_transformation,[],[f3])).
% 2.72/0.94  
% 2.72/0.94  fof(f40,plain,(
% 2.72/0.94    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.72/0.94    inference(cnf_transformation,[],[f17])).
% 2.72/0.94  
% 2.72/0.94  fof(f4,axiom,(
% 2.72/0.94    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f41,plain,(
% 2.72/0.94    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.72/0.94    inference(cnf_transformation,[],[f4])).
% 2.72/0.94  
% 2.72/0.94  fof(f1,axiom,(
% 2.72/0.94    v1_xboole_0(k1_xboole_0)),
% 2.72/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.94  
% 2.72/0.94  fof(f38,plain,(
% 2.72/0.94    v1_xboole_0(k1_xboole_0)),
% 2.72/0.94    inference(cnf_transformation,[],[f1])).
% 2.72/0.94  
% 2.72/0.94  fof(f61,plain,(
% 2.72/0.94    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.72/0.94    inference(cnf_transformation,[],[f37])).
% 2.72/0.94  
% 2.72/0.94  cnf(c_16,negated_conjecture,
% 2.72/0.94      ( m1_subset_1(sK5,sK1) ),
% 2.72/0.94      inference(cnf_transformation,[],[f59]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1182,plain,
% 2.72/0.94      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_17,negated_conjecture,
% 2.72/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.72/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1181,plain,
% 2.72/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_19,negated_conjecture,
% 2.72/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.72/0.94      inference(cnf_transformation,[],[f56]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1179,plain,
% 2.72/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_9,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 2.72/0.94      | ~ v1_funct_1(X3)
% 2.72/0.94      | ~ v1_funct_1(X0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1186,plain,
% 2.72/0.94      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.72/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 2.72/0.94      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 2.72/0.94      | v1_funct_1(X0) != iProver_top
% 2.72/0.94      | v1_funct_1(X3) != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_12,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,X1)
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ v1_funct_1(X0)
% 2.72/0.94      | v1_xboole_0(X1)
% 2.72/0.94      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.72/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1183,plain,
% 2.72/0.94      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 2.72/0.94      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.72/0.94      | v1_funct_1(X2) != iProver_top
% 2.72/0.94      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2473,plain,
% 2.72/0.94      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 2.72/0.94      | v1_funct_2(X3,X0,X2) != iProver_top
% 2.72/0.94      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 2.72/0.94      | m1_subset_1(X5,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.72/0.94      | v1_funct_1(X3) != iProver_top
% 2.72/0.94      | v1_funct_1(X4) != iProver_top
% 2.72/0.94      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 2.72/0.94      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1186,c_1183]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_11,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ v1_funct_1(X3)
% 2.72/0.94      | ~ v1_funct_1(X0)
% 2.72/0.94      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 2.72/0.94      inference(cnf_transformation,[],[f47]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1184,plain,
% 2.72/0.94      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.72/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 2.72/0.94      | v1_funct_1(X0) != iProver_top
% 2.72/0.94      | v1_funct_1(X3) != iProver_top
% 2.72/0.94      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_10,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 2.72/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ v1_funct_1(X4)
% 2.72/0.94      | ~ v1_funct_1(X0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1185,plain,
% 2.72/0.94      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.72/0.94      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 2.72/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.72/0.94      | v1_funct_1(X4) != iProver_top
% 2.72/0.94      | v1_funct_1(X0) != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_4306,plain,
% 2.72/0.94      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 2.72/0.94      | v1_funct_2(X3,X0,X2) != iProver_top
% 2.72/0.94      | m1_subset_1(X5,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.72/0.94      | v1_funct_1(X4) != iProver_top
% 2.72/0.94      | v1_funct_1(X3) != iProver_top
% 2.72/0.94      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.94      inference(forward_subsumption_resolution,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_2473,c_1184,c_1185]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_4313,plain,
% 2.72/0.94      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 2.72/0.94      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,sK1) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top
% 2.72/0.94      | v1_funct_1(sK3) != iProver_top
% 2.72/0.94      | v1_xboole_0(sK1) = iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1179,c_4306]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_22,negated_conjecture,
% 2.72/0.94      ( ~ v1_xboole_0(sK1) ),
% 2.72/0.94      inference(cnf_transformation,[],[f53]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_25,plain,
% 2.72/0.94      ( v1_xboole_0(sK1) != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_21,negated_conjecture,
% 2.72/0.94      ( v1_funct_1(sK3) ),
% 2.72/0.94      inference(cnf_transformation,[],[f54]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_26,plain,
% 2.72/0.94      ( v1_funct_1(sK3) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_20,negated_conjecture,
% 2.72/0.94      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_27,plain,
% 2.72/0.94      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5120,plain,
% 2.72/0.94      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,sK1) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.94      inference(global_propositional_subsumption,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_4313,c_25,c_26,c_27]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5132,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 2.72/0.94      | m1_subset_1(X0,sK1) != iProver_top
% 2.72/0.94      | v1_funct_1(sK4) != iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1181,c_5120]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_18,negated_conjecture,
% 2.72/0.94      ( v1_funct_1(sK4) ),
% 2.72/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_29,plain,
% 2.72/0.94      ( v1_funct_1(sK4) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5173,plain,
% 2.72/0.94      ( m1_subset_1(X0,sK1) != iProver_top
% 2.72/0.94      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 2.72/0.94      inference(global_propositional_subsumption,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_5132,c_29]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5174,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 2.72/0.94      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.72/0.94      inference(renaming,[status(thm)],[c_5173]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5181,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1182,c_5174]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.72/0.94      inference(cnf_transformation,[],[f43]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1188,plain,
% 2.72/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_6,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f44]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1187,plain,
% 2.72/0.94      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.72/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1748,plain,
% 2.72/0.94      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1181,c_1187]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.72/0.94      inference(cnf_transformation,[],[f39]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_13,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,X1)
% 2.72/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 2.72/0.94      | ~ v1_funct_1(X4)
% 2.72/0.94      | ~ v1_funct_1(X0)
% 2.72/0.94      | v1_xboole_0(X2)
% 2.72/0.94      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.72/0.94      | k1_xboole_0 = X1 ),
% 2.72/0.94      inference(cnf_transformation,[],[f51]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_329,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,X1)
% 2.72/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X7)))
% 2.72/0.94      | ~ v1_funct_1(X0)
% 2.72/0.94      | ~ v1_funct_1(X6)
% 2.72/0.94      | v1_xboole_0(X2)
% 2.72/0.94      | k1_relset_1(X2,X7,X6) != X5
% 2.72/0.94      | k2_relset_1(X1,X2,X0) != X4
% 2.72/0.94      | k1_funct_1(k8_funct_2(X1,X2,X7,X0,X6),X3) = k1_funct_1(X6,k1_funct_1(X0,X3))
% 2.72/0.94      | k1_xboole_0 = X1 ),
% 2.72/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_330,plain,
% 2.72/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.94      | ~ m1_subset_1(X3,X1)
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.72/0.94      | ~ m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(k1_relset_1(X2,X5,X4)))
% 2.72/0.94      | ~ v1_funct_1(X0)
% 2.72/0.94      | ~ v1_funct_1(X4)
% 2.72/0.94      | v1_xboole_0(X2)
% 2.72/0.94      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.72/0.94      | k1_xboole_0 = X1 ),
% 2.72/0.94      inference(unflattening,[status(thm)],[c_329]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1172,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | v1_funct_2(X3,X0,X1) != iProver_top
% 2.72/0.94      | m1_subset_1(X5,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.72/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.72/0.94      | m1_subset_1(k2_relset_1(X0,X1,X3),k1_zfmisc_1(k1_relset_1(X1,X2,X4))) != iProver_top
% 2.72/0.94      | v1_funct_1(X4) != iProver_top
% 2.72/0.94      | v1_funct_1(X3) != iProver_top
% 2.72/0.94      | v1_xboole_0(X1) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1755,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.72/0.94      | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 2.72/0.94      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top
% 2.72/0.94      | v1_funct_1(sK4) != iProver_top
% 2.72/0.94      | v1_xboole_0(sK0) = iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1748,c_1172]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_23,negated_conjecture,
% 2.72/0.94      ( ~ v1_xboole_0(sK0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f52]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_24,plain,
% 2.72/0.94      ( v1_xboole_0(sK0) != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_30,plain,
% 2.72/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1909,plain,
% 2.72/0.94      ( m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,X0) != iProver_top
% 2.72/0.94      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 2.72/0.94      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.94      inference(global_propositional_subsumption,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_1755,c_24,c_29,c_30]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1910,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.72/0.94      | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.94      inference(renaming,[status(thm)],[c_1909]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_4,plain,
% 2.72/0.94      ( v4_relat_1(X0,X1)
% 2.72/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.72/0.94      inference(cnf_transformation,[],[f42]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_8,plain,
% 2.72/0.94      ( ~ v1_partfun1(X0,X1)
% 2.72/0.94      | ~ v4_relat_1(X0,X1)
% 2.72/0.94      | ~ v1_relat_1(X0)
% 2.72/0.94      | k1_relat_1(X0) = X1 ),
% 2.72/0.94      inference(cnf_transformation,[],[f45]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_15,negated_conjecture,
% 2.72/0.94      ( v1_partfun1(sK4,sK0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_293,plain,
% 2.72/0.94      ( ~ v4_relat_1(X0,X1)
% 2.72/0.94      | ~ v1_relat_1(X0)
% 2.72/0.94      | k1_relat_1(X0) = X1
% 2.72/0.94      | sK4 != X0
% 2.72/0.94      | sK0 != X1 ),
% 2.72/0.94      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_294,plain,
% 2.72/0.94      ( ~ v4_relat_1(sK4,sK0)
% 2.72/0.94      | ~ v1_relat_1(sK4)
% 2.72/0.94      | k1_relat_1(sK4) = sK0 ),
% 2.72/0.94      inference(unflattening,[status(thm)],[c_293]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_310,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | ~ v1_relat_1(sK4)
% 2.72/0.94      | k1_relat_1(sK4) = sK0
% 2.72/0.94      | sK4 != X0
% 2.72/0.94      | sK0 != X1 ),
% 2.72/0.94      inference(resolution_lifted,[status(thm)],[c_4,c_294]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_311,plain,
% 2.72/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.72/0.94      | ~ v1_relat_1(sK4)
% 2.72/0.94      | k1_relat_1(sK4) = sK0 ),
% 2.72/0.94      inference(unflattening,[status(thm)],[c_310]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_791,plain,
% 2.72/0.94      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 2.72/0.94      inference(splitting,
% 2.72/0.94                [splitting(split),new_symbols(definition,[])],
% 2.72/0.94                [c_311]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1173,plain,
% 2.72/0.94      ( k1_relat_1(sK4) = sK0
% 2.72/0.94      | v1_relat_1(sK4) != iProver_top
% 2.72/0.94      | sP0_iProver_split = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_820,plain,
% 2.72/0.94      ( k1_relat_1(sK4) = sK0
% 2.72/0.94      | v1_relat_1(sK4) != iProver_top
% 2.72/0.94      | sP0_iProver_split = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/0.94      | ~ v1_relat_1(X1)
% 2.72/0.94      | v1_relat_1(X0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1354,plain,
% 2.72/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.94      | v1_relat_1(X0)
% 2.72/0.94      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_2]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1640,plain,
% 2.72/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.72/0.94      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 2.72/0.94      | v1_relat_1(sK4) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1641,plain,
% 2.72/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.72/0.94      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.72/0.94      | v1_relat_1(sK4) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_3,plain,
% 2.72/0.94      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.72/0.94      inference(cnf_transformation,[],[f41]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1765,plain,
% 2.72/0.94      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1766,plain,
% 2.72/0.94      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_790,plain,
% 2.72/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.72/0.94      | ~ sP0_iProver_split ),
% 2.72/0.94      inference(splitting,
% 2.72/0.94                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.72/0.94                [c_311]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1174,plain,
% 2.72/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.72/0.94      | sP0_iProver_split != iProver_top ),
% 2.72/0.94      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1779,plain,
% 2.72/0.94      ( sP0_iProver_split != iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1181,c_1174]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1814,plain,
% 2.72/0.94      ( k1_relat_1(sK4) = sK0 ),
% 2.72/0.94      inference(global_propositional_subsumption,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_1173,c_30,c_820,c_1641,c_1766,c_1779]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1915,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.72/0.94      | m1_subset_1(k2_relset_1(X0,sK0,X1),k1_zfmisc_1(sK0)) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.94      inference(light_normalisation,[status(thm)],[c_1910,c_1814]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2060,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 2.72/0.94      | k1_xboole_0 = X0
% 2.72/0.94      | v1_funct_2(X1,X0,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X2,X0) != iProver_top
% 2.72/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.72/0.94      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1188,c_1915]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2436,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.72/0.94      | sK1 = k1_xboole_0
% 2.72/0.94      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.72/0.94      | m1_subset_1(X0,sK1) != iProver_top
% 2.72/0.94      | v1_funct_1(sK3) != iProver_top ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1179,c_2060]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_0,plain,
% 2.72/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 2.72/0.94      inference(cnf_transformation,[],[f38]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_376,plain,
% 2.72/0.94      ( sK1 != k1_xboole_0 ),
% 2.72/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2860,plain,
% 2.72/0.94      ( m1_subset_1(X0,sK1) != iProver_top
% 2.72/0.94      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
% 2.72/0.94      inference(global_propositional_subsumption,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_2436,c_26,c_27,c_376]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2861,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.72/0.94      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.72/0.94      inference(renaming,[status(thm)],[c_2860]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2868,plain,
% 2.72/0.94      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.94      inference(superposition,[status(thm)],[c_1182,c_2861]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_5182,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.94      inference(light_normalisation,[status(thm)],[c_5181,c_2868]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_794,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1381,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != X0
% 2.72/0.94      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != X0 ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_794]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1491,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(X0,X1)
% 2.72/0.94      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(X0,X1) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1381]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2402,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
% 2.72/0.94      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1491]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_805,plain,
% 2.72/0.94      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 2.72/0.94      theory(equality) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1492,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK0,sK3,sK5) != X0
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(X1,X0)
% 2.72/0.94      | sK4 != X1 ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_805]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1740,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK0,sK3,sK5) != X0
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,X0)
% 2.72/0.94      | sK4 != sK4 ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1492]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_2196,plain,
% 2.72/0.94      ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
% 2.72/0.94      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.72/0.94      | sK4 != sK4 ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1740]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1430,plain,
% 2.72/0.94      ( ~ v1_funct_2(sK3,X0,X1)
% 2.72/0.94      | ~ m1_subset_1(X2,X0)
% 2.72/0.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.72/0.94      | ~ v1_funct_1(sK3)
% 2.72/0.94      | v1_xboole_0(X0)
% 2.72/0.94      | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_12]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1549,plain,
% 2.72/0.94      ( ~ v1_funct_2(sK3,sK1,X0)
% 2.72/0.94      | ~ m1_subset_1(sK5,sK1)
% 2.72/0.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 2.72/0.94      | ~ v1_funct_1(sK3)
% 2.72/0.94      | v1_xboole_0(sK1)
% 2.72/0.94      | k3_funct_2(sK1,X0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1430]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1551,plain,
% 2.72/0.94      ( ~ v1_funct_2(sK3,sK1,sK0)
% 2.72/0.94      | ~ m1_subset_1(sK5,sK1)
% 2.72/0.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.72/0.94      | ~ v1_funct_1(sK3)
% 2.72/0.94      | v1_xboole_0(sK1)
% 2.72/0.94      | k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_1549]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_793,plain,( X0 = X0 ),theory(equality) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_1504,plain,
% 2.72/0.94      ( sK4 = sK4 ),
% 2.72/0.94      inference(instantiation,[status(thm)],[c_793]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(c_14,negated_conjecture,
% 2.72/0.94      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.72/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.72/0.94  
% 2.72/0.94  cnf(contradiction,plain,
% 2.72/0.94      ( $false ),
% 2.72/0.94      inference(minisat,
% 2.72/0.94                [status(thm)],
% 2.72/0.94                [c_5182,c_2402,c_2196,c_1551,c_1504,c_14,c_16,c_19,c_20,
% 2.72/0.94                 c_21,c_22]) ).
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.94  
% 2.72/0.94  ------                               Statistics
% 2.72/0.94  
% 2.72/0.94  ------ General
% 2.72/0.94  
% 2.72/0.94  abstr_ref_over_cycles:                  0
% 2.72/0.94  abstr_ref_under_cycles:                 0
% 2.72/0.94  gc_basic_clause_elim:                   0
% 2.72/0.94  forced_gc_time:                         0
% 2.72/0.94  parsing_time:                           0.009
% 2.72/0.94  unif_index_cands_time:                  0.
% 2.72/0.94  unif_index_add_time:                    0.
% 2.72/0.94  orderings_time:                         0.
% 2.72/0.94  out_proof_time:                         0.011
% 2.72/0.94  total_time:                             0.211
% 2.72/0.94  num_of_symbols:                         55
% 2.72/0.94  num_of_terms:                           8028
% 2.72/0.94  
% 2.72/0.94  ------ Preprocessing
% 2.72/0.94  
% 2.72/0.94  num_of_splits:                          1
% 2.72/0.94  num_of_split_atoms:                     1
% 2.72/0.94  num_of_reused_defs:                     0
% 2.72/0.94  num_eq_ax_congr_red:                    20
% 2.72/0.94  num_of_sem_filtered_clauses:            1
% 2.72/0.94  num_of_subtypes:                        1
% 2.72/0.94  monotx_restored_types:                  0
% 2.72/0.94  sat_num_of_epr_types:                   0
% 2.72/0.94  sat_num_of_non_cyclic_types:            0
% 2.72/0.94  sat_guarded_non_collapsed_types:        1
% 2.72/0.94  num_pure_diseq_elim:                    0
% 2.72/0.94  simp_replaced_by:                       0
% 2.72/0.94  res_preprocessed:                       113
% 2.72/0.94  prep_upred:                             0
% 2.72/0.94  prep_unflattend:                        18
% 2.72/0.94  smt_new_axioms:                         0
% 2.72/0.94  pred_elim_cands:                        5
% 2.72/0.94  pred_elim:                              3
% 2.72/0.94  pred_elim_cl:                           4
% 2.72/0.94  pred_elim_cycles:                       6
% 2.72/0.94  merged_defs:                            0
% 2.72/0.94  merged_defs_ncl:                        0
% 2.72/0.94  bin_hyper_res:                          0
% 2.72/0.94  prep_cycles:                            4
% 2.72/0.94  pred_elim_time:                         0.009
% 2.72/0.94  splitting_time:                         0.
% 2.72/0.94  sem_filter_time:                        0.
% 2.72/0.94  monotx_time:                            0.
% 2.72/0.94  subtype_inf_time:                       0.
% 2.72/0.94  
% 2.72/0.94  ------ Problem properties
% 2.72/0.94  
% 2.72/0.94  clauses:                                21
% 2.72/0.94  conjectures:                            9
% 2.72/0.94  epr:                                    7
% 2.72/0.94  horn:                                   18
% 2.72/0.94  ground:                                 11
% 2.72/0.94  unary:                                  11
% 2.72/0.94  binary:                                 3
% 2.72/0.94  lits:                                   57
% 2.72/0.94  lits_eq:                                6
% 2.72/0.94  fd_pure:                                0
% 2.72/0.94  fd_pseudo:                              0
% 2.72/0.94  fd_cond:                                1
% 2.72/0.94  fd_pseudo_cond:                         0
% 2.72/0.94  ac_symbols:                             0
% 2.72/0.94  
% 2.72/0.94  ------ Propositional Solver
% 2.72/0.94  
% 2.72/0.94  prop_solver_calls:                      28
% 2.72/0.94  prop_fast_solver_calls:                 1085
% 2.72/0.94  smt_solver_calls:                       0
% 2.72/0.94  smt_fast_solver_calls:                  0
% 2.72/0.94  prop_num_of_clauses:                    1985
% 2.72/0.94  prop_preprocess_simplified:             4849
% 2.72/0.94  prop_fo_subsumed:                       39
% 2.72/0.94  prop_solver_time:                       0.
% 2.72/0.94  smt_solver_time:                        0.
% 2.72/0.94  smt_fast_solver_time:                   0.
% 2.72/0.94  prop_fast_solver_time:                  0.
% 2.72/0.94  prop_unsat_core_time:                   0.
% 2.72/0.94  
% 2.72/0.94  ------ QBF
% 2.72/0.94  
% 2.72/0.94  qbf_q_res:                              0
% 2.72/0.94  qbf_num_tautologies:                    0
% 2.72/0.94  qbf_prep_cycles:                        0
% 2.72/0.94  
% 2.72/0.94  ------ BMC1
% 2.72/0.94  
% 2.72/0.94  bmc1_current_bound:                     -1
% 2.72/0.94  bmc1_last_solved_bound:                 -1
% 2.72/0.94  bmc1_unsat_core_size:                   -1
% 2.72/0.94  bmc1_unsat_core_parents_size:           -1
% 2.72/0.94  bmc1_merge_next_fun:                    0
% 2.72/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.94  
% 2.72/0.94  ------ Instantiation
% 2.72/0.94  
% 2.72/0.94  inst_num_of_clauses:                    540
% 2.72/0.94  inst_num_in_passive:                    93
% 2.72/0.94  inst_num_in_active:                     312
% 2.72/0.94  inst_num_in_unprocessed:                135
% 2.72/0.94  inst_num_of_loops:                      320
% 2.72/0.94  inst_num_of_learning_restarts:          0
% 2.72/0.94  inst_num_moves_active_passive:          4
% 2.72/0.94  inst_lit_activity:                      0
% 2.72/0.94  inst_lit_activity_moves:                0
% 2.72/0.94  inst_num_tautologies:                   0
% 2.72/0.94  inst_num_prop_implied:                  0
% 2.72/0.94  inst_num_existing_simplified:           0
% 2.72/0.94  inst_num_eq_res_simplified:             0
% 2.72/0.94  inst_num_child_elim:                    0
% 2.72/0.94  inst_num_of_dismatching_blockings:      75
% 2.72/0.94  inst_num_of_non_proper_insts:           437
% 2.72/0.94  inst_num_of_duplicates:                 0
% 2.72/0.94  inst_inst_num_from_inst_to_res:         0
% 2.72/0.94  inst_dismatching_checking_time:         0.
% 2.72/0.94  
% 2.72/0.94  ------ Resolution
% 2.72/0.94  
% 2.72/0.94  res_num_of_clauses:                     0
% 2.72/0.94  res_num_in_passive:                     0
% 2.72/0.94  res_num_in_active:                      0
% 2.72/0.94  res_num_of_loops:                       117
% 2.72/0.94  res_forward_subset_subsumed:            80
% 2.72/0.94  res_backward_subset_subsumed:           0
% 2.72/0.94  res_forward_subsumed:                   0
% 2.72/0.94  res_backward_subsumed:                  0
% 2.72/0.94  res_forward_subsumption_resolution:     0
% 2.72/0.94  res_backward_subsumption_resolution:    0
% 2.72/0.94  res_clause_to_clause_subsumption:       457
% 2.72/0.94  res_orphan_elimination:                 0
% 2.72/0.94  res_tautology_del:                      69
% 2.72/0.94  res_num_eq_res_simplified:              0
% 2.72/0.94  res_num_sel_changes:                    0
% 2.72/0.94  res_moves_from_active_to_pass:          0
% 2.72/0.94  
% 2.72/0.94  ------ Superposition
% 2.72/0.94  
% 2.72/0.94  sup_time_total:                         0.
% 2.72/0.94  sup_time_generating:                    0.
% 2.72/0.94  sup_time_sim_full:                      0.
% 2.72/0.94  sup_time_sim_immed:                     0.
% 2.72/0.94  
% 2.72/0.94  sup_num_of_clauses:                     94
% 2.72/0.94  sup_num_in_active:                      62
% 2.72/0.94  sup_num_in_passive:                     32
% 2.72/0.94  sup_num_of_loops:                       63
% 2.72/0.94  sup_fw_superposition:                   63
% 2.72/0.94  sup_bw_superposition:                   11
% 2.72/0.94  sup_immediate_simplified:               1
% 2.72/0.94  sup_given_eliminated:                   0
% 2.72/0.94  comparisons_done:                       0
% 2.72/0.94  comparisons_avoided:                    8
% 2.72/0.94  
% 2.72/0.94  ------ Simplifications
% 2.72/0.94  
% 2.72/0.94  
% 2.72/0.94  sim_fw_subset_subsumed:                 0
% 2.72/0.94  sim_bw_subset_subsumed:                 0
% 2.72/0.94  sim_fw_subsumed:                        0
% 2.72/0.94  sim_bw_subsumed:                        0
% 2.72/0.94  sim_fw_subsumption_res:                 6
% 2.72/0.94  sim_bw_subsumption_res:                 0
% 2.72/0.94  sim_tautology_del:                      0
% 2.72/0.94  sim_eq_tautology_del:                   0
% 2.72/0.94  sim_eq_res_simp:                        0
% 2.72/0.94  sim_fw_demodulated:                     0
% 2.72/0.94  sim_bw_demodulated:                     2
% 2.72/0.94  sim_light_normalised:                   2
% 2.72/0.94  sim_joinable_taut:                      0
% 2.72/0.94  sim_joinable_simp:                      0
% 2.72/0.94  sim_ac_normalised:                      0
% 2.72/0.94  sim_smt_subsumption:                    0
% 2.72/0.94  
%------------------------------------------------------------------------------
