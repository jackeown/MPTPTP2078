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
% DateTime   : Thu Dec  3 12:09:42 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1664)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
                   => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
                     => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f39,f55,f54,f53,f52])).

fof(f93,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

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
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1112,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1122,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3079,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1122])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1111,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1120,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2907,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1111,c_1120])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1113,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3428,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2907,c_1113])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1109,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1116,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3743,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1116])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_594,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1376,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1378,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_4175,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3743,c_39,c_41,c_42,c_43,c_5,c_1378,c_1664,c_1988,c_2382])).

cnf(c_4176,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4175])).

cnf(c_4184,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_4176])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1118,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4538,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_1118])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1114,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2681,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1114])).

cnf(c_3654,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_2(sK5,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2681,c_39,c_41,c_42,c_5,c_1378])).

cnf(c_3655,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3654])).

cnf(c_3663,plain,
    ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_3655])).

cnf(c_10798,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4538,c_41,c_3663])).

cnf(c_10799,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10798])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_16,c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_377,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_15])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1104,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1688,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_1104])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1901,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1688,c_44])).

cnf(c_1902,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1901])).

cnf(c_10809,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10799,c_1902])).

cnf(c_11101,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_relat_1(sK6) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3079,c_10809])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_91,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_593,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1394,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_1395,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1483,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1487,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1515,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1516,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_1518,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1703,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1707,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2024,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2025,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_3521,plain,
    ( ~ r2_hidden(sK1(X0,sK3),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3522,plain,
    ( r2_hidden(sK1(X0,sK3),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3521])).

cnf(c_3524,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3522])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_1119,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5276,plain,
    ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1119])).

cnf(c_40,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6954,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5276,c_40,c_44,c_45])).

cnf(c_6955,plain,
    ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6954])).

cnf(c_6966,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_6955])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6998,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6966,c_41,c_42,c_43,c_31,c_82,c_83,c_1395])).

cnf(c_7006,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1112,c_6998])).

cnf(c_30,negated_conjecture,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7141,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_7006,c_30])).

cnf(c_11269,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11101,c_31,c_82,c_83,c_91,c_1395,c_1487,c_1518,c_1707,c_2025,c_3524,c_7141])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4308,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_1123])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_14])).

cnf(c_186,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1105,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_2002,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1105])).

cnf(c_2335,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2002,c_40,c_42])).

cnf(c_5508,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4308,c_40,c_42,c_31,c_82,c_83,c_91,c_1395,c_1487,c_1518,c_1707,c_2002,c_2025,c_3524])).

cnf(c_11294,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11269,c_5508])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11332,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11294,c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11332,c_91])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.04/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.01  
% 4.04/1.01  ------  iProver source info
% 4.04/1.01  
% 4.04/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.01  git: non_committed_changes: false
% 4.04/1.01  git: last_make_outside_of_git: false
% 4.04/1.01  
% 4.04/1.01  ------ 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options
% 4.04/1.01  
% 4.04/1.01  --out_options                           all
% 4.04/1.01  --tptp_safe_out                         true
% 4.04/1.01  --problem_path                          ""
% 4.04/1.01  --include_path                          ""
% 4.04/1.01  --clausifier                            res/vclausify_rel
% 4.04/1.01  --clausifier_options                    --mode clausify
% 4.04/1.01  --stdin                                 false
% 4.04/1.01  --stats_out                             all
% 4.04/1.01  
% 4.04/1.01  ------ General Options
% 4.04/1.01  
% 4.04/1.01  --fof                                   false
% 4.04/1.01  --time_out_real                         305.
% 4.04/1.01  --time_out_virtual                      -1.
% 4.04/1.01  --symbol_type_check                     false
% 4.04/1.01  --clausify_out                          false
% 4.04/1.01  --sig_cnt_out                           false
% 4.04/1.01  --trig_cnt_out                          false
% 4.04/1.01  --trig_cnt_out_tolerance                1.
% 4.04/1.01  --trig_cnt_out_sk_spl                   false
% 4.04/1.01  --abstr_cl_out                          false
% 4.04/1.01  
% 4.04/1.01  ------ Global Options
% 4.04/1.01  
% 4.04/1.01  --schedule                              default
% 4.04/1.01  --add_important_lit                     false
% 4.04/1.01  --prop_solver_per_cl                    1000
% 4.04/1.01  --min_unsat_core                        false
% 4.04/1.01  --soft_assumptions                      false
% 4.04/1.01  --soft_lemma_size                       3
% 4.04/1.01  --prop_impl_unit_size                   0
% 4.04/1.01  --prop_impl_unit                        []
% 4.04/1.01  --share_sel_clauses                     true
% 4.04/1.01  --reset_solvers                         false
% 4.04/1.01  --bc_imp_inh                            [conj_cone]
% 4.04/1.01  --conj_cone_tolerance                   3.
% 4.04/1.01  --extra_neg_conj                        none
% 4.04/1.01  --large_theory_mode                     true
% 4.04/1.01  --prolific_symb_bound                   200
% 4.04/1.01  --lt_threshold                          2000
% 4.04/1.01  --clause_weak_htbl                      true
% 4.04/1.01  --gc_record_bc_elim                     false
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing Options
% 4.04/1.01  
% 4.04/1.01  --preprocessing_flag                    true
% 4.04/1.01  --time_out_prep_mult                    0.1
% 4.04/1.01  --splitting_mode                        input
% 4.04/1.01  --splitting_grd                         true
% 4.04/1.01  --splitting_cvd                         false
% 4.04/1.01  --splitting_cvd_svl                     false
% 4.04/1.01  --splitting_nvd                         32
% 4.04/1.01  --sub_typing                            true
% 4.04/1.01  --prep_gs_sim                           true
% 4.04/1.01  --prep_unflatten                        true
% 4.04/1.01  --prep_res_sim                          true
% 4.04/1.01  --prep_upred                            true
% 4.04/1.01  --prep_sem_filter                       exhaustive
% 4.04/1.01  --prep_sem_filter_out                   false
% 4.04/1.01  --pred_elim                             true
% 4.04/1.01  --res_sim_input                         true
% 4.04/1.01  --eq_ax_congr_red                       true
% 4.04/1.01  --pure_diseq_elim                       true
% 4.04/1.01  --brand_transform                       false
% 4.04/1.01  --non_eq_to_eq                          false
% 4.04/1.01  --prep_def_merge                        true
% 4.04/1.01  --prep_def_merge_prop_impl              false
% 4.04/1.01  --prep_def_merge_mbd                    true
% 4.04/1.01  --prep_def_merge_tr_red                 false
% 4.04/1.01  --prep_def_merge_tr_cl                  false
% 4.04/1.01  --smt_preprocessing                     true
% 4.04/1.01  --smt_ac_axioms                         fast
% 4.04/1.01  --preprocessed_out                      false
% 4.04/1.01  --preprocessed_stats                    false
% 4.04/1.01  
% 4.04/1.01  ------ Abstraction refinement Options
% 4.04/1.01  
% 4.04/1.01  --abstr_ref                             []
% 4.04/1.01  --abstr_ref_prep                        false
% 4.04/1.01  --abstr_ref_until_sat                   false
% 4.04/1.01  --abstr_ref_sig_restrict                funpre
% 4.04/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.01  --abstr_ref_under                       []
% 4.04/1.01  
% 4.04/1.01  ------ SAT Options
% 4.04/1.01  
% 4.04/1.01  --sat_mode                              false
% 4.04/1.01  --sat_fm_restart_options                ""
% 4.04/1.01  --sat_gr_def                            false
% 4.04/1.01  --sat_epr_types                         true
% 4.04/1.01  --sat_non_cyclic_types                  false
% 4.04/1.01  --sat_finite_models                     false
% 4.04/1.01  --sat_fm_lemmas                         false
% 4.04/1.01  --sat_fm_prep                           false
% 4.04/1.01  --sat_fm_uc_incr                        true
% 4.04/1.01  --sat_out_model                         small
% 4.04/1.01  --sat_out_clauses                       false
% 4.04/1.01  
% 4.04/1.01  ------ QBF Options
% 4.04/1.01  
% 4.04/1.01  --qbf_mode                              false
% 4.04/1.01  --qbf_elim_univ                         false
% 4.04/1.01  --qbf_dom_inst                          none
% 4.04/1.01  --qbf_dom_pre_inst                      false
% 4.04/1.01  --qbf_sk_in                             false
% 4.04/1.01  --qbf_pred_elim                         true
% 4.04/1.01  --qbf_split                             512
% 4.04/1.01  
% 4.04/1.01  ------ BMC1 Options
% 4.04/1.01  
% 4.04/1.01  --bmc1_incremental                      false
% 4.04/1.01  --bmc1_axioms                           reachable_all
% 4.04/1.01  --bmc1_min_bound                        0
% 4.04/1.01  --bmc1_max_bound                        -1
% 4.04/1.01  --bmc1_max_bound_default                -1
% 4.04/1.01  --bmc1_symbol_reachability              true
% 4.04/1.01  --bmc1_property_lemmas                  false
% 4.04/1.01  --bmc1_k_induction                      false
% 4.04/1.01  --bmc1_non_equiv_states                 false
% 4.04/1.01  --bmc1_deadlock                         false
% 4.04/1.01  --bmc1_ucm                              false
% 4.04/1.01  --bmc1_add_unsat_core                   none
% 4.04/1.01  --bmc1_unsat_core_children              false
% 4.04/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.01  --bmc1_out_stat                         full
% 4.04/1.01  --bmc1_ground_init                      false
% 4.04/1.01  --bmc1_pre_inst_next_state              false
% 4.04/1.01  --bmc1_pre_inst_state                   false
% 4.04/1.01  --bmc1_pre_inst_reach_state             false
% 4.04/1.01  --bmc1_out_unsat_core                   false
% 4.04/1.01  --bmc1_aig_witness_out                  false
% 4.04/1.01  --bmc1_verbose                          false
% 4.04/1.01  --bmc1_dump_clauses_tptp                false
% 4.04/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.01  --bmc1_dump_file                        -
% 4.04/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.01  --bmc1_ucm_extend_mode                  1
% 4.04/1.01  --bmc1_ucm_init_mode                    2
% 4.04/1.01  --bmc1_ucm_cone_mode                    none
% 4.04/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.01  --bmc1_ucm_relax_model                  4
% 4.04/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.01  --bmc1_ucm_layered_model                none
% 4.04/1.01  --bmc1_ucm_max_lemma_size               10
% 4.04/1.01  
% 4.04/1.01  ------ AIG Options
% 4.04/1.01  
% 4.04/1.01  --aig_mode                              false
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation Options
% 4.04/1.01  
% 4.04/1.01  --instantiation_flag                    true
% 4.04/1.01  --inst_sos_flag                         false
% 4.04/1.01  --inst_sos_phase                        true
% 4.04/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel_side                     num_symb
% 4.04/1.01  --inst_solver_per_active                1400
% 4.04/1.01  --inst_solver_calls_frac                1.
% 4.04/1.01  --inst_passive_queue_type               priority_queues
% 4.04/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.01  --inst_passive_queues_freq              [25;2]
% 4.04/1.01  --inst_dismatching                      true
% 4.04/1.01  --inst_eager_unprocessed_to_passive     true
% 4.04/1.01  --inst_prop_sim_given                   true
% 4.04/1.01  --inst_prop_sim_new                     false
% 4.04/1.01  --inst_subs_new                         false
% 4.04/1.01  --inst_eq_res_simp                      false
% 4.04/1.01  --inst_subs_given                       false
% 4.04/1.01  --inst_orphan_elimination               true
% 4.04/1.01  --inst_learning_loop_flag               true
% 4.04/1.01  --inst_learning_start                   3000
% 4.04/1.01  --inst_learning_factor                  2
% 4.04/1.01  --inst_start_prop_sim_after_learn       3
% 4.04/1.01  --inst_sel_renew                        solver
% 4.04/1.01  --inst_lit_activity_flag                true
% 4.04/1.01  --inst_restr_to_given                   false
% 4.04/1.01  --inst_activity_threshold               500
% 4.04/1.01  --inst_out_proof                        true
% 4.04/1.01  
% 4.04/1.01  ------ Resolution Options
% 4.04/1.01  
% 4.04/1.01  --resolution_flag                       true
% 4.04/1.01  --res_lit_sel                           adaptive
% 4.04/1.01  --res_lit_sel_side                      none
% 4.04/1.01  --res_ordering                          kbo
% 4.04/1.01  --res_to_prop_solver                    active
% 4.04/1.01  --res_prop_simpl_new                    false
% 4.04/1.01  --res_prop_simpl_given                  true
% 4.04/1.01  --res_passive_queue_type                priority_queues
% 4.04/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.01  --res_passive_queues_freq               [15;5]
% 4.04/1.01  --res_forward_subs                      full
% 4.04/1.01  --res_backward_subs                     full
% 4.04/1.01  --res_forward_subs_resolution           true
% 4.04/1.01  --res_backward_subs_resolution          true
% 4.04/1.01  --res_orphan_elimination                true
% 4.04/1.01  --res_time_limit                        2.
% 4.04/1.01  --res_out_proof                         true
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Options
% 4.04/1.01  
% 4.04/1.01  --superposition_flag                    true
% 4.04/1.01  --sup_passive_queue_type                priority_queues
% 4.04/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.01  --demod_completeness_check              fast
% 4.04/1.01  --demod_use_ground                      true
% 4.04/1.01  --sup_to_prop_solver                    passive
% 4.04/1.01  --sup_prop_simpl_new                    true
% 4.04/1.01  --sup_prop_simpl_given                  true
% 4.04/1.01  --sup_fun_splitting                     false
% 4.04/1.01  --sup_smt_interval                      50000
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Simplification Setup
% 4.04/1.01  
% 4.04/1.01  --sup_indices_passive                   []
% 4.04/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_full_bw                           [BwDemod]
% 4.04/1.01  --sup_immed_triv                        [TrivRules]
% 4.04/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_immed_bw_main                     []
% 4.04/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.01  
% 4.04/1.01  ------ Combination Options
% 4.04/1.01  
% 4.04/1.01  --comb_res_mult                         3
% 4.04/1.01  --comb_sup_mult                         2
% 4.04/1.01  --comb_inst_mult                        10
% 4.04/1.01  
% 4.04/1.01  ------ Debug Options
% 4.04/1.01  
% 4.04/1.01  --dbg_backtrace                         false
% 4.04/1.01  --dbg_dump_prop_clauses                 false
% 4.04/1.01  --dbg_dump_prop_clauses_file            -
% 4.04/1.01  --dbg_out_stat                          false
% 4.04/1.01  ------ Parsing...
% 4.04/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.01  ------ Proving...
% 4.04/1.01  ------ Problem Properties 
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  clauses                                 33
% 4.04/1.01  conjectures                             10
% 4.04/1.01  EPR                                     13
% 4.04/1.01  Horn                                    24
% 4.04/1.01  unary                                   14
% 4.04/1.01  binary                                  6
% 4.04/1.01  lits                                    88
% 4.04/1.01  lits eq                                 15
% 4.04/1.01  fd_pure                                 0
% 4.04/1.01  fd_pseudo                               0
% 4.04/1.01  fd_cond                                 5
% 4.04/1.01  fd_pseudo_cond                          1
% 4.04/1.01  AC symbols                              0
% 4.04/1.01  
% 4.04/1.01  ------ Schedule dynamic 5 is on 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  ------ 
% 4.04/1.01  Current options:
% 4.04/1.01  ------ 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options
% 4.04/1.01  
% 4.04/1.01  --out_options                           all
% 4.04/1.01  --tptp_safe_out                         true
% 4.04/1.01  --problem_path                          ""
% 4.04/1.01  --include_path                          ""
% 4.04/1.01  --clausifier                            res/vclausify_rel
% 4.04/1.01  --clausifier_options                    --mode clausify
% 4.04/1.01  --stdin                                 false
% 4.04/1.01  --stats_out                             all
% 4.04/1.01  
% 4.04/1.01  ------ General Options
% 4.04/1.01  
% 4.04/1.01  --fof                                   false
% 4.04/1.01  --time_out_real                         305.
% 4.04/1.01  --time_out_virtual                      -1.
% 4.04/1.01  --symbol_type_check                     false
% 4.04/1.01  --clausify_out                          false
% 4.04/1.01  --sig_cnt_out                           false
% 4.04/1.01  --trig_cnt_out                          false
% 4.04/1.01  --trig_cnt_out_tolerance                1.
% 4.04/1.01  --trig_cnt_out_sk_spl                   false
% 4.04/1.01  --abstr_cl_out                          false
% 4.04/1.01  
% 4.04/1.01  ------ Global Options
% 4.04/1.01  
% 4.04/1.01  --schedule                              default
% 4.04/1.01  --add_important_lit                     false
% 4.04/1.01  --prop_solver_per_cl                    1000
% 4.04/1.01  --min_unsat_core                        false
% 4.04/1.01  --soft_assumptions                      false
% 4.04/1.01  --soft_lemma_size                       3
% 4.04/1.01  --prop_impl_unit_size                   0
% 4.04/1.01  --prop_impl_unit                        []
% 4.04/1.01  --share_sel_clauses                     true
% 4.04/1.01  --reset_solvers                         false
% 4.04/1.01  --bc_imp_inh                            [conj_cone]
% 4.04/1.01  --conj_cone_tolerance                   3.
% 4.04/1.01  --extra_neg_conj                        none
% 4.04/1.01  --large_theory_mode                     true
% 4.04/1.01  --prolific_symb_bound                   200
% 4.04/1.01  --lt_threshold                          2000
% 4.04/1.01  --clause_weak_htbl                      true
% 4.04/1.01  --gc_record_bc_elim                     false
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing Options
% 4.04/1.01  
% 4.04/1.01  --preprocessing_flag                    true
% 4.04/1.01  --time_out_prep_mult                    0.1
% 4.04/1.01  --splitting_mode                        input
% 4.04/1.01  --splitting_grd                         true
% 4.04/1.01  --splitting_cvd                         false
% 4.04/1.01  --splitting_cvd_svl                     false
% 4.04/1.01  --splitting_nvd                         32
% 4.04/1.01  --sub_typing                            true
% 4.04/1.01  --prep_gs_sim                           true
% 4.04/1.01  --prep_unflatten                        true
% 4.04/1.01  --prep_res_sim                          true
% 4.04/1.01  --prep_upred                            true
% 4.04/1.01  --prep_sem_filter                       exhaustive
% 4.04/1.01  --prep_sem_filter_out                   false
% 4.04/1.01  --pred_elim                             true
% 4.04/1.01  --res_sim_input                         true
% 4.04/1.01  --eq_ax_congr_red                       true
% 4.04/1.01  --pure_diseq_elim                       true
% 4.04/1.01  --brand_transform                       false
% 4.04/1.01  --non_eq_to_eq                          false
% 4.04/1.01  --prep_def_merge                        true
% 4.04/1.01  --prep_def_merge_prop_impl              false
% 4.04/1.01  --prep_def_merge_mbd                    true
% 4.04/1.01  --prep_def_merge_tr_red                 false
% 4.04/1.01  --prep_def_merge_tr_cl                  false
% 4.04/1.01  --smt_preprocessing                     true
% 4.04/1.01  --smt_ac_axioms                         fast
% 4.04/1.01  --preprocessed_out                      false
% 4.04/1.01  --preprocessed_stats                    false
% 4.04/1.01  
% 4.04/1.01  ------ Abstraction refinement Options
% 4.04/1.01  
% 4.04/1.01  --abstr_ref                             []
% 4.04/1.01  --abstr_ref_prep                        false
% 4.04/1.01  --abstr_ref_until_sat                   false
% 4.04/1.01  --abstr_ref_sig_restrict                funpre
% 4.04/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.01  --abstr_ref_under                       []
% 4.04/1.01  
% 4.04/1.01  ------ SAT Options
% 4.04/1.01  
% 4.04/1.01  --sat_mode                              false
% 4.04/1.01  --sat_fm_restart_options                ""
% 4.04/1.01  --sat_gr_def                            false
% 4.04/1.01  --sat_epr_types                         true
% 4.04/1.01  --sat_non_cyclic_types                  false
% 4.04/1.01  --sat_finite_models                     false
% 4.04/1.01  --sat_fm_lemmas                         false
% 4.04/1.01  --sat_fm_prep                           false
% 4.04/1.01  --sat_fm_uc_incr                        true
% 4.04/1.01  --sat_out_model                         small
% 4.04/1.01  --sat_out_clauses                       false
% 4.04/1.01  
% 4.04/1.01  ------ QBF Options
% 4.04/1.01  
% 4.04/1.01  --qbf_mode                              false
% 4.04/1.01  --qbf_elim_univ                         false
% 4.04/1.01  --qbf_dom_inst                          none
% 4.04/1.01  --qbf_dom_pre_inst                      false
% 4.04/1.01  --qbf_sk_in                             false
% 4.04/1.01  --qbf_pred_elim                         true
% 4.04/1.01  --qbf_split                             512
% 4.04/1.01  
% 4.04/1.01  ------ BMC1 Options
% 4.04/1.01  
% 4.04/1.01  --bmc1_incremental                      false
% 4.04/1.01  --bmc1_axioms                           reachable_all
% 4.04/1.01  --bmc1_min_bound                        0
% 4.04/1.01  --bmc1_max_bound                        -1
% 4.04/1.01  --bmc1_max_bound_default                -1
% 4.04/1.01  --bmc1_symbol_reachability              true
% 4.04/1.01  --bmc1_property_lemmas                  false
% 4.04/1.01  --bmc1_k_induction                      false
% 4.04/1.01  --bmc1_non_equiv_states                 false
% 4.04/1.01  --bmc1_deadlock                         false
% 4.04/1.01  --bmc1_ucm                              false
% 4.04/1.01  --bmc1_add_unsat_core                   none
% 4.04/1.01  --bmc1_unsat_core_children              false
% 4.04/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.01  --bmc1_out_stat                         full
% 4.04/1.01  --bmc1_ground_init                      false
% 4.04/1.01  --bmc1_pre_inst_next_state              false
% 4.04/1.01  --bmc1_pre_inst_state                   false
% 4.04/1.01  --bmc1_pre_inst_reach_state             false
% 4.04/1.01  --bmc1_out_unsat_core                   false
% 4.04/1.01  --bmc1_aig_witness_out                  false
% 4.04/1.01  --bmc1_verbose                          false
% 4.04/1.01  --bmc1_dump_clauses_tptp                false
% 4.04/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.01  --bmc1_dump_file                        -
% 4.04/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.01  --bmc1_ucm_extend_mode                  1
% 4.04/1.01  --bmc1_ucm_init_mode                    2
% 4.04/1.01  --bmc1_ucm_cone_mode                    none
% 4.04/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.01  --bmc1_ucm_relax_model                  4
% 4.04/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.01  --bmc1_ucm_layered_model                none
% 4.04/1.01  --bmc1_ucm_max_lemma_size               10
% 4.04/1.01  
% 4.04/1.01  ------ AIG Options
% 4.04/1.01  
% 4.04/1.01  --aig_mode                              false
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation Options
% 4.04/1.01  
% 4.04/1.01  --instantiation_flag                    true
% 4.04/1.01  --inst_sos_flag                         false
% 4.04/1.01  --inst_sos_phase                        true
% 4.04/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel_side                     none
% 4.04/1.01  --inst_solver_per_active                1400
% 4.04/1.01  --inst_solver_calls_frac                1.
% 4.04/1.01  --inst_passive_queue_type               priority_queues
% 4.04/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.01  --inst_passive_queues_freq              [25;2]
% 4.04/1.01  --inst_dismatching                      true
% 4.04/1.01  --inst_eager_unprocessed_to_passive     true
% 4.04/1.01  --inst_prop_sim_given                   true
% 4.04/1.01  --inst_prop_sim_new                     false
% 4.04/1.01  --inst_subs_new                         false
% 4.04/1.01  --inst_eq_res_simp                      false
% 4.04/1.01  --inst_subs_given                       false
% 4.04/1.01  --inst_orphan_elimination               true
% 4.04/1.01  --inst_learning_loop_flag               true
% 4.04/1.01  --inst_learning_start                   3000
% 4.04/1.01  --inst_learning_factor                  2
% 4.04/1.01  --inst_start_prop_sim_after_learn       3
% 4.04/1.01  --inst_sel_renew                        solver
% 4.04/1.01  --inst_lit_activity_flag                true
% 4.04/1.01  --inst_restr_to_given                   false
% 4.04/1.01  --inst_activity_threshold               500
% 4.04/1.01  --inst_out_proof                        true
% 4.04/1.01  
% 4.04/1.01  ------ Resolution Options
% 4.04/1.01  
% 4.04/1.01  --resolution_flag                       false
% 4.04/1.01  --res_lit_sel                           adaptive
% 4.04/1.01  --res_lit_sel_side                      none
% 4.04/1.01  --res_ordering                          kbo
% 4.04/1.01  --res_to_prop_solver                    active
% 4.04/1.01  --res_prop_simpl_new                    false
% 4.04/1.01  --res_prop_simpl_given                  true
% 4.04/1.01  --res_passive_queue_type                priority_queues
% 4.04/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.01  --res_passive_queues_freq               [15;5]
% 4.04/1.01  --res_forward_subs                      full
% 4.04/1.01  --res_backward_subs                     full
% 4.04/1.01  --res_forward_subs_resolution           true
% 4.04/1.01  --res_backward_subs_resolution          true
% 4.04/1.01  --res_orphan_elimination                true
% 4.04/1.01  --res_time_limit                        2.
% 4.04/1.01  --res_out_proof                         true
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Options
% 4.04/1.01  
% 4.04/1.01  --superposition_flag                    true
% 4.04/1.01  --sup_passive_queue_type                priority_queues
% 4.04/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.01  --demod_completeness_check              fast
% 4.04/1.01  --demod_use_ground                      true
% 4.04/1.01  --sup_to_prop_solver                    passive
% 4.04/1.01  --sup_prop_simpl_new                    true
% 4.04/1.01  --sup_prop_simpl_given                  true
% 4.04/1.01  --sup_fun_splitting                     false
% 4.04/1.01  --sup_smt_interval                      50000
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Simplification Setup
% 4.04/1.01  
% 4.04/1.01  --sup_indices_passive                   []
% 4.04/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_full_bw                           [BwDemod]
% 4.04/1.01  --sup_immed_triv                        [TrivRules]
% 4.04/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_immed_bw_main                     []
% 4.04/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.01  
% 4.04/1.01  ------ Combination Options
% 4.04/1.01  
% 4.04/1.01  --comb_res_mult                         3
% 4.04/1.01  --comb_sup_mult                         2
% 4.04/1.01  --comb_inst_mult                        10
% 4.04/1.01  
% 4.04/1.01  ------ Debug Options
% 4.04/1.01  
% 4.04/1.01  --dbg_backtrace                         false
% 4.04/1.01  --dbg_dump_prop_clauses                 false
% 4.04/1.01  --dbg_dump_prop_clauses_file            -
% 4.04/1.01  --dbg_out_stat                          false
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  ------ Proving...
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  % SZS status Theorem for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  fof(f17,conjecture,(
% 4.04/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f18,negated_conjecture,(
% 4.04/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 4.04/1.01    inference(negated_conjecture,[],[f17])).
% 4.04/1.01  
% 4.04/1.01  fof(f38,plain,(
% 4.04/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 4.04/1.01    inference(ennf_transformation,[],[f18])).
% 4.04/1.01  
% 4.04/1.01  fof(f39,plain,(
% 4.04/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 4.04/1.01    inference(flattening,[],[f38])).
% 4.04/1.01  
% 4.04/1.01  fof(f55,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f54,plain,(
% 4.04/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f53,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f52,plain,(
% 4.04/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f56,plain,(
% 4.04/1.01    (((k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f39,f55,f54,f53,f52])).
% 4.04/1.01  
% 4.04/1.01  fof(f93,plain,(
% 4.04/1.01    m1_subset_1(sK7,sK3)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f7,axiom,(
% 4.04/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f22,plain,(
% 4.04/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 4.04/1.01    inference(ennf_transformation,[],[f7])).
% 4.04/1.01  
% 4.04/1.01  fof(f23,plain,(
% 4.04/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 4.04/1.01    inference(flattening,[],[f22])).
% 4.04/1.01  
% 4.04/1.01  fof(f70,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f23])).
% 4.04/1.01  
% 4.04/1.01  fof(f92,plain,(
% 4.04/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f11,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f27,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.01    inference(ennf_transformation,[],[f11])).
% 4.04/1.01  
% 4.04/1.01  fof(f74,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f27])).
% 4.04/1.01  
% 4.04/1.01  fof(f94,plain,(
% 4.04/1.01    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f90,plain,(
% 4.04/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f16,axiom,(
% 4.04/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f36,plain,(
% 4.04/1.01    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.04/1.01    inference(ennf_transformation,[],[f16])).
% 4.04/1.01  
% 4.04/1.01  fof(f37,plain,(
% 4.04/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.04/1.01    inference(flattening,[],[f36])).
% 4.04/1.01  
% 4.04/1.01  fof(f85,plain,(
% 4.04/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f37])).
% 4.04/1.01  
% 4.04/1.01  fof(f87,plain,(
% 4.04/1.01    ~v1_xboole_0(sK4)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f88,plain,(
% 4.04/1.01    v1_funct_1(sK5)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f89,plain,(
% 4.04/1.01    v1_funct_2(sK5,sK3,sK4)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f3,axiom,(
% 4.04/1.01    v1_xboole_0(k1_xboole_0)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f62,plain,(
% 4.04/1.01    v1_xboole_0(k1_xboole_0)),
% 4.04/1.01    inference(cnf_transformation,[],[f3])).
% 4.04/1.01  
% 4.04/1.01  fof(f15,axiom,(
% 4.04/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f34,plain,(
% 4.04/1.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.04/1.01    inference(ennf_transformation,[],[f15])).
% 4.04/1.01  
% 4.04/1.01  fof(f35,plain,(
% 4.04/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.04/1.01    inference(flattening,[],[f34])).
% 4.04/1.01  
% 4.04/1.01  fof(f80,plain,(
% 4.04/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f35])).
% 4.04/1.01  
% 4.04/1.01  fof(f83,plain,(
% 4.04/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f37])).
% 4.04/1.01  
% 4.04/1.01  fof(f10,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f19,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.04/1.01    inference(pure_predicate_removal,[],[f10])).
% 4.04/1.01  
% 4.04/1.01  fof(f26,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.01    inference(ennf_transformation,[],[f19])).
% 4.04/1.01  
% 4.04/1.01  fof(f73,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f26])).
% 4.04/1.01  
% 4.04/1.01  fof(f13,axiom,(
% 4.04/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f30,plain,(
% 4.04/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.04/1.01    inference(ennf_transformation,[],[f13])).
% 4.04/1.01  
% 4.04/1.01  fof(f31,plain,(
% 4.04/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.04/1.01    inference(flattening,[],[f30])).
% 4.04/1.01  
% 4.04/1.01  fof(f78,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f31])).
% 4.04/1.01  
% 4.04/1.01  fof(f9,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f25,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.01    inference(ennf_transformation,[],[f9])).
% 4.04/1.01  
% 4.04/1.01  fof(f72,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f25])).
% 4.04/1.01  
% 4.04/1.01  fof(f91,plain,(
% 4.04/1.01    v1_funct_1(sK6)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f95,plain,(
% 4.04/1.01    k1_xboole_0 != sK3),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f5,axiom,(
% 4.04/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f50,plain,(
% 4.04/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.04/1.01    inference(nnf_transformation,[],[f5])).
% 4.04/1.01  
% 4.04/1.01  fof(f51,plain,(
% 4.04/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.04/1.01    inference(flattening,[],[f50])).
% 4.04/1.01  
% 4.04/1.01  fof(f66,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f51])).
% 4.04/1.01  
% 4.04/1.01  fof(f67,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.04/1.01    inference(cnf_transformation,[],[f51])).
% 4.04/1.01  
% 4.04/1.01  fof(f100,plain,(
% 4.04/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.04/1.01    inference(equality_resolution,[],[f67])).
% 4.04/1.01  
% 4.04/1.01  fof(f2,axiom,(
% 4.04/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f20,plain,(
% 4.04/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.04/1.01    inference(ennf_transformation,[],[f2])).
% 4.04/1.01  
% 4.04/1.01  fof(f44,plain,(
% 4.04/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/1.01    inference(nnf_transformation,[],[f20])).
% 4.04/1.01  
% 4.04/1.01  fof(f45,plain,(
% 4.04/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/1.01    inference(rectify,[],[f44])).
% 4.04/1.01  
% 4.04/1.01  fof(f46,plain,(
% 4.04/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f47,plain,(
% 4.04/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 4.04/1.01  
% 4.04/1.01  fof(f60,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f47])).
% 4.04/1.01  
% 4.04/1.01  fof(f4,axiom,(
% 4.04/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f48,plain,(
% 4.04/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.01    inference(nnf_transformation,[],[f4])).
% 4.04/1.01  
% 4.04/1.01  fof(f49,plain,(
% 4.04/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.01    inference(flattening,[],[f48])).
% 4.04/1.01  
% 4.04/1.01  fof(f65,plain,(
% 4.04/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f49])).
% 4.04/1.01  
% 4.04/1.01  fof(f1,axiom,(
% 4.04/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f40,plain,(
% 4.04/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.04/1.01    inference(nnf_transformation,[],[f1])).
% 4.04/1.01  
% 4.04/1.01  fof(f41,plain,(
% 4.04/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.04/1.01    inference(rectify,[],[f40])).
% 4.04/1.01  
% 4.04/1.01  fof(f42,plain,(
% 4.04/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f43,plain,(
% 4.04/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 4.04/1.01  
% 4.04/1.01  fof(f57,plain,(
% 4.04/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f43])).
% 4.04/1.01  
% 4.04/1.01  fof(f14,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f32,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 4.04/1.01    inference(ennf_transformation,[],[f14])).
% 4.04/1.01  
% 4.04/1.01  fof(f33,plain,(
% 4.04/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 4.04/1.01    inference(flattening,[],[f32])).
% 4.04/1.01  
% 4.04/1.01  fof(f79,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f33])).
% 4.04/1.01  
% 4.04/1.01  fof(f96,plain,(
% 4.04/1.01    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 4.04/1.01    inference(cnf_transformation,[],[f56])).
% 4.04/1.01  
% 4.04/1.01  fof(f6,axiom,(
% 4.04/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f21,plain,(
% 4.04/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.04/1.01    inference(ennf_transformation,[],[f6])).
% 4.04/1.01  
% 4.04/1.01  fof(f69,plain,(
% 4.04/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f21])).
% 4.04/1.01  
% 4.04/1.01  fof(f12,axiom,(
% 4.04/1.01    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f28,plain,(
% 4.04/1.01    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.04/1.01    inference(ennf_transformation,[],[f12])).
% 4.04/1.01  
% 4.04/1.01  fof(f29,plain,(
% 4.04/1.01    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/1.01    inference(flattening,[],[f28])).
% 4.04/1.01  
% 4.04/1.01  fof(f76,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f29])).
% 4.04/1.01  
% 4.04/1.01  fof(f8,axiom,(
% 4.04/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f24,plain,(
% 4.04/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 4.04/1.01    inference(ennf_transformation,[],[f8])).
% 4.04/1.01  
% 4.04/1.01  fof(f71,plain,(
% 4.04/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f24])).
% 4.04/1.01  
% 4.04/1.01  fof(f68,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.04/1.01    inference(cnf_transformation,[],[f51])).
% 4.04/1.01  
% 4.04/1.01  fof(f99,plain,(
% 4.04/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.04/1.01    inference(equality_resolution,[],[f68])).
% 4.04/1.01  
% 4.04/1.01  cnf(c_33,negated_conjecture,
% 4.04/1.01      ( m1_subset_1(sK7,sK3) ),
% 4.04/1.01      inference(cnf_transformation,[],[f93]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1112,plain,
% 4.04/1.01      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_13,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.04/1.01      inference(cnf_transformation,[],[f70]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1122,plain,
% 4.04/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 4.04/1.01      | r2_hidden(X0,X1) = iProver_top
% 4.04/1.01      | v1_xboole_0(X1) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3079,plain,
% 4.04/1.01      ( r2_hidden(sK7,sK3) = iProver_top
% 4.04/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1112,c_1122]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_34,negated_conjecture,
% 4.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f92]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1111,plain,
% 4.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_17,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f74]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1120,plain,
% 4.04/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2907,plain,
% 4.04/1.01      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1111,c_1120]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_32,negated_conjecture,
% 4.04/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 4.04/1.01      inference(cnf_transformation,[],[f94]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1113,plain,
% 4.04/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3428,plain,
% 4.04/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_2907,c_1113]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_36,negated_conjecture,
% 4.04/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f90]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1109,plain,
% 4.04/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_25,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 4.04/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k1_xboole_0 = X2 ),
% 4.04/1.01      inference(cnf_transformation,[],[f85]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1116,plain,
% 4.04/1.01      ( k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3743,plain,
% 4.04/1.01      ( sK4 = k1_xboole_0
% 4.04/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 4.04/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 4.04/1.01      | v1_funct_1(sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1109,c_1116]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_39,negated_conjecture,
% 4.04/1.01      ( ~ v1_xboole_0(sK4) ),
% 4.04/1.01      inference(cnf_transformation,[],[f87]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_38,negated_conjecture,
% 4.04/1.01      ( v1_funct_1(sK5) ),
% 4.04/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_41,plain,
% 4.04/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_37,negated_conjecture,
% 4.04/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 4.04/1.01      inference(cnf_transformation,[],[f89]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_42,plain,
% 4.04/1.01      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_5,plain,
% 4.04/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f62]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_594,plain,
% 4.04/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 4.04/1.01      theory(equality) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1376,plain,
% 4.04/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_594]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1378,plain,
% 4.04/1.01      ( v1_xboole_0(sK4)
% 4.04/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 4.04/1.01      | sK4 != k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1376]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4175,plain,
% 4.04/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 4.04/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_3743,c_39,c_41,c_42,c_43,c_5,c_1378,c_1664,c_1988,
% 4.04/1.01                 c_2382]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4176,plain,
% 4.04/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_4175]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4184,plain,
% 4.04/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3428,c_4176]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_23,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ r2_hidden(X3,X1)
% 4.04/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k1_xboole_0 = X2 ),
% 4.04/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1118,plain,
% 4.04/1.01      ( k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.04/1.01      | r2_hidden(X3,X2) != iProver_top
% 4.04/1.01      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4538,plain,
% 4.04/1.01      ( k1_relat_1(sK6) = k1_xboole_0
% 4.04/1.01      | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | r2_hidden(X0,sK3) != iProver_top
% 4.04/1.01      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 4.04/1.01      | v1_funct_1(sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_4184,c_1118]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_27,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | v1_funct_2(X0,X1,X3)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k1_xboole_0 = X2 ),
% 4.04/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1114,plain,
% 4.04/1.01      ( k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.04/1.01      | v1_funct_2(X1,X2,X3) = iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2681,plain,
% 4.04/1.01      ( sK4 = k1_xboole_0
% 4.04/1.01      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 4.04/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 4.04/1.01      | v1_funct_1(sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1109,c_1114]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3654,plain,
% 4.04/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 4.04/1.01      | v1_funct_2(sK5,sK3,X0) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_2681,c_39,c_41,c_42,c_5,c_1378]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3655,plain,
% 4.04/1.01      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_3654]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3663,plain,
% 4.04/1.01      ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3428,c_3655]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10798,plain,
% 4.04/1.01      ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 4.04/1.01      | r2_hidden(X0,sK3) != iProver_top
% 4.04/1.01      | k1_relat_1(sK6) = k1_xboole_0 ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_4538,c_41,c_3663]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10799,plain,
% 4.04/1.01      ( k1_relat_1(sK6) = k1_xboole_0
% 4.04/1.01      | r2_hidden(X0,sK3) != iProver_top
% 4.04/1.01      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_10798]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_16,plain,
% 4.04/1.01      ( v5_relat_1(X0,X1)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f73]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_21,plain,
% 4.04/1.01      ( ~ v5_relat_1(X0,X1)
% 4.04/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 4.04/1.01      | ~ v1_relat_1(X0)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 4.04/1.01      inference(cnf_transformation,[],[f78]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_373,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 4.04/1.01      | ~ v1_relat_1(X0)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.04/1.01      inference(resolution,[status(thm)],[c_16,c_21]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_15,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | v1_relat_1(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_377,plain,
% 4.04/1.01      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_373,c_15]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_378,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_377]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1104,plain,
% 4.04/1.01      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 4.04/1.01      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1688,plain,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 4.04/1.01      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | v1_funct_1(sK6) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1111,c_1104]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_35,negated_conjecture,
% 4.04/1.01      ( v1_funct_1(sK6) ),
% 4.04/1.01      inference(cnf_transformation,[],[f91]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_44,plain,
% 4.04/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1901,plain,
% 4.04/1.01      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_1688,c_44]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1902,plain,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 4.04/1.01      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_1901]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10809,plain,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 4.04/1.01      | k1_relat_1(sK6) = k1_xboole_0
% 4.04/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_10799,c_1902]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11101,plain,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 4.04/1.01      | k1_relat_1(sK6) = k1_xboole_0
% 4.04/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3079,c_10809]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_31,negated_conjecture,
% 4.04/1.01      ( k1_xboole_0 != sK3 ),
% 4.04/1.01      inference(cnf_transformation,[],[f95]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11,plain,
% 4.04/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 4.04/1.01      | k1_xboole_0 = X1
% 4.04/1.01      | k1_xboole_0 = X0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_82,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.04/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_10,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f100]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_83,plain,
% 4.04/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_91,plain,
% 4.04/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_593,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1394,plain,
% 4.04/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_593]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1395,plain,
% 4.04/1.01      ( sK3 != k1_xboole_0
% 4.04/1.01      | k1_xboole_0 = sK3
% 4.04/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1394]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3,plain,
% 4.04/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1483,plain,
% 4.04/1.01      ( r1_tarski(sK3,k1_xboole_0)
% 4.04/1.01      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1487,plain,
% 4.04/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 4.04/1.01      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6,plain,
% 4.04/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f65]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1515,plain,
% 4.04/1.01      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1516,plain,
% 4.04/1.01      ( sK3 = X0
% 4.04/1.01      | r1_tarski(X0,sK3) != iProver_top
% 4.04/1.01      | r1_tarski(sK3,X0) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1518,plain,
% 4.04/1.01      ( sK3 = k1_xboole_0
% 4.04/1.01      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 4.04/1.01      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1516]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1703,plain,
% 4.04/1.01      ( r1_tarski(k1_xboole_0,sK3)
% 4.04/1.01      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1707,plain,
% 4.04/1.01      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 4.04/1.01      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1,plain,
% 4.04/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.04/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2024,plain,
% 4.04/1.01      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2025,plain,
% 4.04/1.01      ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
% 4.04/1.01      | v1_xboole_0(sK3) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3521,plain,
% 4.04/1.01      ( ~ r2_hidden(sK1(X0,sK3),X0) | ~ v1_xboole_0(X0) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3522,plain,
% 4.04/1.01      ( r2_hidden(sK1(X0,sK3),X0) != iProver_top
% 4.04/1.01      | v1_xboole_0(X0) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_3521]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3524,plain,
% 4.04/1.01      ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
% 4.04/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_3522]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_22,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ m1_subset_1(X3,X1)
% 4.04/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 4.04/1.01      | ~ v1_funct_1(X4)
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | v1_xboole_0(X2)
% 4.04/1.01      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 4.04/1.01      | k1_xboole_0 = X1 ),
% 4.04/1.01      inference(cnf_transformation,[],[f79]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1119,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 4.04/1.01      | k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X3,X0,X1) != iProver_top
% 4.04/1.01      | m1_subset_1(X5,X0) != iProver_top
% 4.04/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 4.04/1.01      | v1_funct_1(X3) != iProver_top
% 4.04/1.01      | v1_funct_1(X4) != iProver_top
% 4.04/1.01      | v1_xboole_0(X1) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_5276,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 4.04/1.01      | k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X1,X0,sK4) != iProver_top
% 4.04/1.01      | m1_subset_1(X2,X0) != iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 4.04/1.01      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top
% 4.04/1.01      | v1_funct_1(sK6) != iProver_top
% 4.04/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2907,c_1119]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_40,plain,
% 4.04/1.01      ( v1_xboole_0(sK4) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_45,plain,
% 4.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6954,plain,
% 4.04/1.01      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 4.04/1.01      | m1_subset_1(X2,X0) != iProver_top
% 4.04/1.01      | v1_funct_2(X1,X0,sK4) != iProver_top
% 4.04/1.01      | k1_xboole_0 = X0
% 4.04/1.01      | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 4.04/1.01      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_5276,c_40,c_44,c_45]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6955,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 4.04/1.01      | k1_xboole_0 = X0
% 4.04/1.01      | v1_funct_2(X1,X0,sK4) != iProver_top
% 4.04/1.01      | m1_subset_1(X2,X0) != iProver_top
% 4.04/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 4.04/1.01      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 4.04/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_6954]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6966,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 4.04/1.01      | sK3 = k1_xboole_0
% 4.04/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 4.04/1.01      | m1_subset_1(X0,sK3) != iProver_top
% 4.04/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 4.04/1.01      | v1_funct_1(sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3428,c_6955]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_43,plain,
% 4.04/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6998,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 4.04/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_6966,c_41,c_42,c_43,c_31,c_82,c_83,c_1395]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_7006,plain,
% 4.04/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1112,c_6998]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_30,negated_conjecture,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 4.04/1.01      inference(cnf_transformation,[],[f96]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_7141,plain,
% 4.04/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_7006,c_30]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11269,plain,
% 4.04/1.01      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_11101,c_31,c_82,c_83,c_91,c_1395,c_1487,c_1518,c_1707,
% 4.04/1.01                 c_2025,c_3524,c_7141]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_12,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/1.01      | ~ v1_xboole_0(X1)
% 4.04/1.01      | v1_xboole_0(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1123,plain,
% 4.04/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/1.01      | v1_xboole_0(X1) != iProver_top
% 4.04/1.01      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4308,plain,
% 4.04/1.01      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top
% 4.04/1.01      | v1_xboole_0(sK5) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_4184,c_1123]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_19,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ v1_funct_1(X0)
% 4.04/1.01      | ~ v1_xboole_0(X0)
% 4.04/1.01      | v1_xboole_0(X1)
% 4.04/1.01      | v1_xboole_0(X2) ),
% 4.04/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_14,plain,
% 4.04/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 4.04/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_185,plain,
% 4.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ v1_xboole_0(X0)
% 4.04/1.01      | v1_xboole_0(X1)
% 4.04/1.01      | v1_xboole_0(X2) ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_19,c_14]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_186,plain,
% 4.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.01      | ~ v1_xboole_0(X0)
% 4.04/1.01      | v1_xboole_0(X1)
% 4.04/1.01      | v1_xboole_0(X2) ),
% 4.04/1.01      inference(renaming,[status(thm)],[c_185]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1105,plain,
% 4.04/1.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 4.04/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.04/1.01      | v1_xboole_0(X0) != iProver_top
% 4.04/1.01      | v1_xboole_0(X2) = iProver_top
% 4.04/1.01      | v1_xboole_0(X1) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2002,plain,
% 4.04/1.01      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 4.04/1.01      | v1_xboole_0(sK4) = iProver_top
% 4.04/1.01      | v1_xboole_0(sK3) = iProver_top
% 4.04/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1109,c_1105]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2335,plain,
% 4.04/1.01      ( v1_xboole_0(sK3) = iProver_top
% 4.04/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_2002,c_40,c_42]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_5508,plain,
% 4.04/1.01      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_4308,c_40,c_42,c_31,c_82,c_83,c_91,c_1395,c_1487,
% 4.04/1.01                 c_1518,c_1707,c_2002,c_2025,c_3524]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11294,plain,
% 4.04/1.01      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_11269,c_5508]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_9,plain,
% 4.04/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f99]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11332,plain,
% 4.04/1.01      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_11294,c_9]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(contradiction,plain,
% 4.04/1.01      ( $false ),
% 4.04/1.01      inference(minisat,[status(thm)],[c_11332,c_91]) ).
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  ------                               Statistics
% 4.04/1.01  
% 4.04/1.01  ------ General
% 4.04/1.01  
% 4.04/1.01  abstr_ref_over_cycles:                  0
% 4.04/1.01  abstr_ref_under_cycles:                 0
% 4.04/1.01  gc_basic_clause_elim:                   0
% 4.04/1.01  forced_gc_time:                         0
% 4.04/1.01  parsing_time:                           0.01
% 4.04/1.01  unif_index_cands_time:                  0.
% 4.04/1.01  unif_index_add_time:                    0.
% 4.04/1.01  orderings_time:                         0.
% 4.04/1.01  out_proof_time:                         0.019
% 4.04/1.01  total_time:                             0.465
% 4.04/1.01  num_of_symbols:                         56
% 4.04/1.01  num_of_terms:                           11320
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing
% 4.04/1.01  
% 4.04/1.01  num_of_splits:                          0
% 4.04/1.01  num_of_split_atoms:                     0
% 4.04/1.01  num_of_reused_defs:                     0
% 4.04/1.01  num_eq_ax_congr_red:                    15
% 4.04/1.01  num_of_sem_filtered_clauses:            1
% 4.04/1.01  num_of_subtypes:                        0
% 4.04/1.01  monotx_restored_types:                  0
% 4.04/1.01  sat_num_of_epr_types:                   0
% 4.04/1.01  sat_num_of_non_cyclic_types:            0
% 4.04/1.01  sat_guarded_non_collapsed_types:        0
% 4.04/1.01  num_pure_diseq_elim:                    0
% 4.04/1.01  simp_replaced_by:                       0
% 4.04/1.01  res_preprocessed:                       165
% 4.04/1.01  prep_upred:                             0
% 4.04/1.01  prep_unflattend:                        0
% 4.04/1.01  smt_new_axioms:                         0
% 4.04/1.01  pred_elim_cands:                        6
% 4.04/1.01  pred_elim:                              2
% 4.04/1.01  pred_elim_cl:                           2
% 4.04/1.01  pred_elim_cycles:                       5
% 4.04/1.01  merged_defs:                            0
% 4.04/1.01  merged_defs_ncl:                        0
% 4.04/1.01  bin_hyper_res:                          0
% 4.04/1.01  prep_cycles:                            4
% 4.04/1.01  pred_elim_time:                         0.003
% 4.04/1.01  splitting_time:                         0.
% 4.04/1.01  sem_filter_time:                        0.
% 4.04/1.01  monotx_time:                            0.001
% 4.04/1.01  subtype_inf_time:                       0.
% 4.04/1.01  
% 4.04/1.01  ------ Problem properties
% 4.04/1.01  
% 4.04/1.01  clauses:                                33
% 4.04/1.01  conjectures:                            10
% 4.04/1.01  epr:                                    13
% 4.04/1.01  horn:                                   24
% 4.04/1.01  ground:                                 11
% 4.04/1.01  unary:                                  14
% 4.04/1.01  binary:                                 6
% 4.04/1.01  lits:                                   88
% 4.04/1.01  lits_eq:                                15
% 4.04/1.01  fd_pure:                                0
% 4.04/1.01  fd_pseudo:                              0
% 4.04/1.01  fd_cond:                                5
% 4.04/1.01  fd_pseudo_cond:                         1
% 4.04/1.01  ac_symbols:                             0
% 4.04/1.01  
% 4.04/1.01  ------ Propositional Solver
% 4.04/1.01  
% 4.04/1.01  prop_solver_calls:                      28
% 4.04/1.01  prop_fast_solver_calls:                 1448
% 4.04/1.01  smt_solver_calls:                       0
% 4.04/1.01  smt_fast_solver_calls:                  0
% 4.04/1.01  prop_num_of_clauses:                    4340
% 4.04/1.01  prop_preprocess_simplified:             10386
% 4.04/1.01  prop_fo_subsumed:                       57
% 4.04/1.01  prop_solver_time:                       0.
% 4.04/1.01  smt_solver_time:                        0.
% 4.04/1.01  smt_fast_solver_time:                   0.
% 4.04/1.01  prop_fast_solver_time:                  0.
% 4.04/1.01  prop_unsat_core_time:                   0.
% 4.04/1.01  
% 4.04/1.01  ------ QBF
% 4.04/1.01  
% 4.04/1.01  qbf_q_res:                              0
% 4.04/1.01  qbf_num_tautologies:                    0
% 4.04/1.01  qbf_prep_cycles:                        0
% 4.04/1.01  
% 4.04/1.01  ------ BMC1
% 4.04/1.01  
% 4.04/1.01  bmc1_current_bound:                     -1
% 4.04/1.01  bmc1_last_solved_bound:                 -1
% 4.04/1.01  bmc1_unsat_core_size:                   -1
% 4.04/1.01  bmc1_unsat_core_parents_size:           -1
% 4.04/1.01  bmc1_merge_next_fun:                    0
% 4.04/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation
% 4.04/1.01  
% 4.04/1.01  inst_num_of_clauses:                    1496
% 4.04/1.01  inst_num_in_passive:                    282
% 4.04/1.01  inst_num_in_active:                     550
% 4.04/1.01  inst_num_in_unprocessed:                664
% 4.04/1.01  inst_num_of_loops:                      710
% 4.04/1.01  inst_num_of_learning_restarts:          0
% 4.04/1.01  inst_num_moves_active_passive:          156
% 4.04/1.01  inst_lit_activity:                      0
% 4.04/1.01  inst_lit_activity_moves:                0
% 4.04/1.01  inst_num_tautologies:                   0
% 4.04/1.01  inst_num_prop_implied:                  0
% 4.04/1.01  inst_num_existing_simplified:           0
% 4.04/1.01  inst_num_eq_res_simplified:             0
% 4.04/1.01  inst_num_child_elim:                    0
% 4.04/1.01  inst_num_of_dismatching_blockings:      323
% 4.04/1.01  inst_num_of_non_proper_insts:           1089
% 4.04/1.01  inst_num_of_duplicates:                 0
% 4.04/1.01  inst_inst_num_from_inst_to_res:         0
% 4.04/1.01  inst_dismatching_checking_time:         0.
% 4.04/1.01  
% 4.04/1.01  ------ Resolution
% 4.04/1.01  
% 4.04/1.01  res_num_of_clauses:                     0
% 4.04/1.01  res_num_in_passive:                     0
% 4.04/1.01  res_num_in_active:                      0
% 4.04/1.01  res_num_of_loops:                       169
% 4.04/1.01  res_forward_subset_subsumed:            147
% 4.04/1.01  res_backward_subset_subsumed:           4
% 4.04/1.01  res_forward_subsumed:                   0
% 4.04/1.01  res_backward_subsumed:                  0
% 4.04/1.01  res_forward_subsumption_resolution:     0
% 4.04/1.01  res_backward_subsumption_resolution:    0
% 4.04/1.01  res_clause_to_clause_subsumption:       550
% 4.04/1.01  res_orphan_elimination:                 0
% 4.04/1.01  res_tautology_del:                      66
% 4.04/1.01  res_num_eq_res_simplified:              0
% 4.04/1.01  res_num_sel_changes:                    0
% 4.04/1.01  res_moves_from_active_to_pass:          0
% 4.04/1.01  
% 4.04/1.01  ------ Superposition
% 4.04/1.01  
% 4.04/1.01  sup_time_total:                         0.
% 4.04/1.01  sup_time_generating:                    0.
% 4.04/1.01  sup_time_sim_full:                      0.
% 4.04/1.01  sup_time_sim_immed:                     0.
% 4.04/1.01  
% 4.04/1.01  sup_num_of_clauses:                     187
% 4.04/1.01  sup_num_in_active:                      96
% 4.04/1.01  sup_num_in_passive:                     91
% 4.04/1.01  sup_num_of_loops:                       140
% 4.04/1.01  sup_fw_superposition:                   117
% 4.04/1.01  sup_bw_superposition:                   132
% 4.04/1.01  sup_immediate_simplified:               21
% 4.04/1.01  sup_given_eliminated:                   0
% 4.04/1.01  comparisons_done:                       0
% 4.04/1.01  comparisons_avoided:                    38
% 4.04/1.01  
% 4.04/1.01  ------ Simplifications
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  sim_fw_subset_subsumed:                 16
% 4.04/1.01  sim_bw_subset_subsumed:                 25
% 4.04/1.01  sim_fw_subsumed:                        7
% 4.04/1.01  sim_bw_subsumed:                        0
% 4.04/1.01  sim_fw_subsumption_res:                 0
% 4.04/1.01  sim_bw_subsumption_res:                 0
% 4.04/1.01  sim_tautology_del:                      9
% 4.04/1.01  sim_eq_tautology_del:                   14
% 4.04/1.01  sim_eq_res_simp:                        0
% 4.04/1.01  sim_fw_demodulated:                     7
% 4.04/1.01  sim_bw_demodulated:                     34
% 4.04/1.01  sim_light_normalised:                   0
% 4.04/1.01  sim_joinable_taut:                      0
% 4.04/1.01  sim_joinable_simp:                      0
% 4.04/1.01  sim_ac_normalised:                      0
% 4.04/1.01  sim_smt_subsumption:                    0
% 4.04/1.01  
%------------------------------------------------------------------------------
