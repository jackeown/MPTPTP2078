%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:44 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1748)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f40,f56,f55,f54,f53])).

fof(f95,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1150,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3808,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_1162])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_93,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_588,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1463,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1464,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1566,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1567,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1605,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1606,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1605])).

cnf(c_1608,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_1788,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1789,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2228,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2229,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2228])).

cnf(c_4020,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4021,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4020])).

cnf(c_4192,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_32,c_84,c_85,c_93,c_1464,c_1567,c_1608,c_1789,c_2229,c_4021])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1149,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1158,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2780,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1149,c_1158])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1151,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3162,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2780,c_1151])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1147,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1154,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3768,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1154])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_589,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1436,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_1438,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_4924,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3768,c_40,c_42,c_43,c_44,c_5,c_1438,c_1748,c_2173,c_2594])).

cnf(c_4925,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4924])).

cnf(c_4933,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_4925])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1156,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5011,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4933,c_1156])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2613,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1152])).

cnf(c_3625,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_2(sK5,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2613,c_40,c_42,c_43,c_5,c_1438])).

cnf(c_3626,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3625])).

cnf(c_3634,plain,
    ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3626])).

cnf(c_10858,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5011,c_42,c_3634])).

cnf(c_10859,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10858])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_17,c_22])).

cnf(c_1142,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1760,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1142])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1948,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | v1_relat_1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1760,c_45])).

cnf(c_1949,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1948])).

cnf(c_10869,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10859,c_1949])).

cnf(c_46,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1811,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2555,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2556,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2555])).

cnf(c_10909,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k1_relat_1(sK6) = k1_xboole_0
    | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10869,c_46,c_1811,c_2556])).

cnf(c_10910,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10909])).

cnf(c_10920,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4192,c_10910])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_1157,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5201,plain,
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
    inference(superposition,[status(thm)],[c_2780,c_1157])).

cnf(c_41,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5912,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5201,c_41,c_45,c_46])).

cnf(c_5913,plain,
    ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5912])).

cnf(c_5923,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_5913])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5928,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5923,c_42,c_43,c_44,c_32,c_84,c_85,c_1464])).

cnf(c_5936,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1150,c_5928])).

cnf(c_31,negated_conjecture,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6196,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_5936,c_31])).

cnf(c_11002,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10920,c_6196])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5007,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4933,c_1163])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_16])).

cnf(c_190,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_1143,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_2103,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1143])).

cnf(c_2390,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2103,c_41,c_43])).

cnf(c_6190,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_41,c_43,c_32,c_84,c_85,c_93,c_1464,c_1567,c_1608,c_1789,c_2103,c_2229,c_4021])).

cnf(c_11022,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11002,c_6190])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11080,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11022,c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11080,c_93])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:39:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.79/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.00  
% 3.79/1.00  ------  iProver source info
% 3.79/1.00  
% 3.79/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.00  git: non_committed_changes: false
% 3.79/1.00  git: last_make_outside_of_git: false
% 3.79/1.00  
% 3.79/1.00  ------ 
% 3.79/1.00  
% 3.79/1.00  ------ Input Options
% 3.79/1.00  
% 3.79/1.00  --out_options                           all
% 3.79/1.00  --tptp_safe_out                         true
% 3.79/1.00  --problem_path                          ""
% 3.79/1.00  --include_path                          ""
% 3.79/1.00  --clausifier                            res/vclausify_rel
% 3.79/1.00  --clausifier_options                    --mode clausify
% 3.79/1.00  --stdin                                 false
% 3.79/1.00  --stats_out                             all
% 3.79/1.00  
% 3.79/1.00  ------ General Options
% 3.79/1.00  
% 3.79/1.00  --fof                                   false
% 3.79/1.00  --time_out_real                         305.
% 3.79/1.00  --time_out_virtual                      -1.
% 3.79/1.00  --symbol_type_check                     false
% 3.79/1.00  --clausify_out                          false
% 3.79/1.00  --sig_cnt_out                           false
% 3.79/1.00  --trig_cnt_out                          false
% 3.79/1.00  --trig_cnt_out_tolerance                1.
% 3.79/1.00  --trig_cnt_out_sk_spl                   false
% 3.79/1.00  --abstr_cl_out                          false
% 3.79/1.00  
% 3.79/1.00  ------ Global Options
% 3.79/1.00  
% 3.79/1.00  --schedule                              default
% 3.79/1.00  --add_important_lit                     false
% 3.79/1.00  --prop_solver_per_cl                    1000
% 3.79/1.00  --min_unsat_core                        false
% 3.79/1.00  --soft_assumptions                      false
% 3.79/1.00  --soft_lemma_size                       3
% 3.79/1.00  --prop_impl_unit_size                   0
% 3.79/1.00  --prop_impl_unit                        []
% 3.79/1.00  --share_sel_clauses                     true
% 3.79/1.00  --reset_solvers                         false
% 3.79/1.00  --bc_imp_inh                            [conj_cone]
% 3.79/1.00  --conj_cone_tolerance                   3.
% 3.79/1.00  --extra_neg_conj                        none
% 3.79/1.00  --large_theory_mode                     true
% 3.79/1.00  --prolific_symb_bound                   200
% 3.79/1.00  --lt_threshold                          2000
% 3.79/1.00  --clause_weak_htbl                      true
% 3.79/1.00  --gc_record_bc_elim                     false
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing Options
% 3.79/1.00  
% 3.79/1.00  --preprocessing_flag                    true
% 3.79/1.00  --time_out_prep_mult                    0.1
% 3.79/1.00  --splitting_mode                        input
% 3.79/1.00  --splitting_grd                         true
% 3.79/1.00  --splitting_cvd                         false
% 3.79/1.00  --splitting_cvd_svl                     false
% 3.79/1.00  --splitting_nvd                         32
% 3.79/1.00  --sub_typing                            true
% 3.79/1.00  --prep_gs_sim                           true
% 3.79/1.00  --prep_unflatten                        true
% 3.79/1.00  --prep_res_sim                          true
% 3.79/1.00  --prep_upred                            true
% 3.79/1.00  --prep_sem_filter                       exhaustive
% 3.79/1.00  --prep_sem_filter_out                   false
% 3.79/1.00  --pred_elim                             true
% 3.79/1.00  --res_sim_input                         true
% 3.79/1.00  --eq_ax_congr_red                       true
% 3.79/1.00  --pure_diseq_elim                       true
% 3.79/1.00  --brand_transform                       false
% 3.79/1.00  --non_eq_to_eq                          false
% 3.79/1.00  --prep_def_merge                        true
% 3.79/1.00  --prep_def_merge_prop_impl              false
% 3.79/1.00  --prep_def_merge_mbd                    true
% 3.79/1.00  --prep_def_merge_tr_red                 false
% 3.79/1.00  --prep_def_merge_tr_cl                  false
% 3.79/1.00  --smt_preprocessing                     true
% 3.79/1.00  --smt_ac_axioms                         fast
% 3.79/1.00  --preprocessed_out                      false
% 3.79/1.00  --preprocessed_stats                    false
% 3.79/1.00  
% 3.79/1.00  ------ Abstraction refinement Options
% 3.79/1.00  
% 3.79/1.00  --abstr_ref                             []
% 3.79/1.00  --abstr_ref_prep                        false
% 3.79/1.00  --abstr_ref_until_sat                   false
% 3.79/1.00  --abstr_ref_sig_restrict                funpre
% 3.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.00  --abstr_ref_under                       []
% 3.79/1.00  
% 3.79/1.00  ------ SAT Options
% 3.79/1.00  
% 3.79/1.00  --sat_mode                              false
% 3.79/1.00  --sat_fm_restart_options                ""
% 3.79/1.00  --sat_gr_def                            false
% 3.79/1.00  --sat_epr_types                         true
% 3.79/1.00  --sat_non_cyclic_types                  false
% 3.79/1.00  --sat_finite_models                     false
% 3.79/1.00  --sat_fm_lemmas                         false
% 3.79/1.00  --sat_fm_prep                           false
% 3.79/1.00  --sat_fm_uc_incr                        true
% 3.79/1.00  --sat_out_model                         small
% 3.79/1.00  --sat_out_clauses                       false
% 3.79/1.00  
% 3.79/1.00  ------ QBF Options
% 3.79/1.00  
% 3.79/1.00  --qbf_mode                              false
% 3.79/1.00  --qbf_elim_univ                         false
% 3.79/1.00  --qbf_dom_inst                          none
% 3.79/1.00  --qbf_dom_pre_inst                      false
% 3.79/1.00  --qbf_sk_in                             false
% 3.79/1.00  --qbf_pred_elim                         true
% 3.79/1.00  --qbf_split                             512
% 3.79/1.00  
% 3.79/1.00  ------ BMC1 Options
% 3.79/1.00  
% 3.79/1.00  --bmc1_incremental                      false
% 3.79/1.00  --bmc1_axioms                           reachable_all
% 3.79/1.00  --bmc1_min_bound                        0
% 3.79/1.00  --bmc1_max_bound                        -1
% 3.79/1.00  --bmc1_max_bound_default                -1
% 3.79/1.00  --bmc1_symbol_reachability              true
% 3.79/1.00  --bmc1_property_lemmas                  false
% 3.79/1.00  --bmc1_k_induction                      false
% 3.79/1.00  --bmc1_non_equiv_states                 false
% 3.79/1.00  --bmc1_deadlock                         false
% 3.79/1.00  --bmc1_ucm                              false
% 3.79/1.00  --bmc1_add_unsat_core                   none
% 3.79/1.00  --bmc1_unsat_core_children              false
% 3.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.00  --bmc1_out_stat                         full
% 3.79/1.00  --bmc1_ground_init                      false
% 3.79/1.00  --bmc1_pre_inst_next_state              false
% 3.79/1.00  --bmc1_pre_inst_state                   false
% 3.79/1.00  --bmc1_pre_inst_reach_state             false
% 3.79/1.00  --bmc1_out_unsat_core                   false
% 3.79/1.00  --bmc1_aig_witness_out                  false
% 3.79/1.00  --bmc1_verbose                          false
% 3.79/1.00  --bmc1_dump_clauses_tptp                false
% 3.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.00  --bmc1_dump_file                        -
% 3.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.00  --bmc1_ucm_extend_mode                  1
% 3.79/1.00  --bmc1_ucm_init_mode                    2
% 3.79/1.00  --bmc1_ucm_cone_mode                    none
% 3.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.00  --bmc1_ucm_relax_model                  4
% 3.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.00  --bmc1_ucm_layered_model                none
% 3.79/1.00  --bmc1_ucm_max_lemma_size               10
% 3.79/1.00  
% 3.79/1.00  ------ AIG Options
% 3.79/1.00  
% 3.79/1.00  --aig_mode                              false
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation Options
% 3.79/1.00  
% 3.79/1.00  --instantiation_flag                    true
% 3.79/1.00  --inst_sos_flag                         false
% 3.79/1.00  --inst_sos_phase                        true
% 3.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel_side                     num_symb
% 3.79/1.00  --inst_solver_per_active                1400
% 3.79/1.00  --inst_solver_calls_frac                1.
% 3.79/1.00  --inst_passive_queue_type               priority_queues
% 3.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.00  --inst_passive_queues_freq              [25;2]
% 3.79/1.00  --inst_dismatching                      true
% 3.79/1.00  --inst_eager_unprocessed_to_passive     true
% 3.79/1.00  --inst_prop_sim_given                   true
% 3.79/1.00  --inst_prop_sim_new                     false
% 3.79/1.00  --inst_subs_new                         false
% 3.79/1.00  --inst_eq_res_simp                      false
% 3.79/1.00  --inst_subs_given                       false
% 3.79/1.00  --inst_orphan_elimination               true
% 3.79/1.00  --inst_learning_loop_flag               true
% 3.79/1.00  --inst_learning_start                   3000
% 3.79/1.00  --inst_learning_factor                  2
% 3.79/1.00  --inst_start_prop_sim_after_learn       3
% 3.79/1.00  --inst_sel_renew                        solver
% 3.79/1.00  --inst_lit_activity_flag                true
% 3.79/1.00  --inst_restr_to_given                   false
% 3.79/1.00  --inst_activity_threshold               500
% 3.79/1.00  --inst_out_proof                        true
% 3.79/1.00  
% 3.79/1.00  ------ Resolution Options
% 3.79/1.00  
% 3.79/1.00  --resolution_flag                       true
% 3.79/1.00  --res_lit_sel                           adaptive
% 3.79/1.00  --res_lit_sel_side                      none
% 3.79/1.00  --res_ordering                          kbo
% 3.79/1.00  --res_to_prop_solver                    active
% 3.79/1.00  --res_prop_simpl_new                    false
% 3.79/1.00  --res_prop_simpl_given                  true
% 3.79/1.00  --res_passive_queue_type                priority_queues
% 3.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.00  --res_passive_queues_freq               [15;5]
% 3.79/1.00  --res_forward_subs                      full
% 3.79/1.00  --res_backward_subs                     full
% 3.79/1.00  --res_forward_subs_resolution           true
% 3.79/1.00  --res_backward_subs_resolution          true
% 3.79/1.00  --res_orphan_elimination                true
% 3.79/1.00  --res_time_limit                        2.
% 3.79/1.00  --res_out_proof                         true
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Options
% 3.79/1.00  
% 3.79/1.00  --superposition_flag                    true
% 3.79/1.00  --sup_passive_queue_type                priority_queues
% 3.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.00  --demod_completeness_check              fast
% 3.79/1.00  --demod_use_ground                      true
% 3.79/1.00  --sup_to_prop_solver                    passive
% 3.79/1.00  --sup_prop_simpl_new                    true
% 3.79/1.00  --sup_prop_simpl_given                  true
% 3.79/1.00  --sup_fun_splitting                     false
% 3.79/1.00  --sup_smt_interval                      50000
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Simplification Setup
% 3.79/1.00  
% 3.79/1.00  --sup_indices_passive                   []
% 3.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_full_bw                           [BwDemod]
% 3.79/1.00  --sup_immed_triv                        [TrivRules]
% 3.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_immed_bw_main                     []
% 3.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  
% 3.79/1.00  ------ Combination Options
% 3.79/1.00  
% 3.79/1.00  --comb_res_mult                         3
% 3.79/1.00  --comb_sup_mult                         2
% 3.79/1.00  --comb_inst_mult                        10
% 3.79/1.00  
% 3.79/1.00  ------ Debug Options
% 3.79/1.00  
% 3.79/1.00  --dbg_backtrace                         false
% 3.79/1.00  --dbg_dump_prop_clauses                 false
% 3.79/1.00  --dbg_dump_prop_clauses_file            -
% 3.79/1.00  --dbg_out_stat                          false
% 3.79/1.00  ------ Parsing...
% 3.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.00  ------ Proving...
% 3.79/1.00  ------ Problem Properties 
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  clauses                                 35
% 3.79/1.00  conjectures                             10
% 3.79/1.00  EPR                                     13
% 3.79/1.00  Horn                                    26
% 3.79/1.00  unary                                   15
% 3.79/1.00  binary                                  6
% 3.79/1.00  lits                                    93
% 3.79/1.00  lits eq                                 15
% 3.79/1.00  fd_pure                                 0
% 3.79/1.00  fd_pseudo                               0
% 3.79/1.00  fd_cond                                 5
% 3.79/1.00  fd_pseudo_cond                          1
% 3.79/1.00  AC symbols                              0
% 3.79/1.00  
% 3.79/1.00  ------ Schedule dynamic 5 is on 
% 3.79/1.00  
% 3.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ 
% 3.79/1.00  Current options:
% 3.79/1.00  ------ 
% 3.79/1.00  
% 3.79/1.00  ------ Input Options
% 3.79/1.00  
% 3.79/1.00  --out_options                           all
% 3.79/1.00  --tptp_safe_out                         true
% 3.79/1.00  --problem_path                          ""
% 3.79/1.00  --include_path                          ""
% 3.79/1.00  --clausifier                            res/vclausify_rel
% 3.79/1.00  --clausifier_options                    --mode clausify
% 3.79/1.00  --stdin                                 false
% 3.79/1.00  --stats_out                             all
% 3.79/1.00  
% 3.79/1.00  ------ General Options
% 3.79/1.00  
% 3.79/1.00  --fof                                   false
% 3.79/1.00  --time_out_real                         305.
% 3.79/1.00  --time_out_virtual                      -1.
% 3.79/1.00  --symbol_type_check                     false
% 3.79/1.00  --clausify_out                          false
% 3.79/1.00  --sig_cnt_out                           false
% 3.79/1.00  --trig_cnt_out                          false
% 3.79/1.00  --trig_cnt_out_tolerance                1.
% 3.79/1.00  --trig_cnt_out_sk_spl                   false
% 3.79/1.00  --abstr_cl_out                          false
% 3.79/1.00  
% 3.79/1.00  ------ Global Options
% 3.79/1.00  
% 3.79/1.00  --schedule                              default
% 3.79/1.00  --add_important_lit                     false
% 3.79/1.00  --prop_solver_per_cl                    1000
% 3.79/1.00  --min_unsat_core                        false
% 3.79/1.00  --soft_assumptions                      false
% 3.79/1.00  --soft_lemma_size                       3
% 3.79/1.00  --prop_impl_unit_size                   0
% 3.79/1.00  --prop_impl_unit                        []
% 3.79/1.00  --share_sel_clauses                     true
% 3.79/1.00  --reset_solvers                         false
% 3.79/1.00  --bc_imp_inh                            [conj_cone]
% 3.79/1.00  --conj_cone_tolerance                   3.
% 3.79/1.00  --extra_neg_conj                        none
% 3.79/1.00  --large_theory_mode                     true
% 3.79/1.00  --prolific_symb_bound                   200
% 3.79/1.00  --lt_threshold                          2000
% 3.79/1.00  --clause_weak_htbl                      true
% 3.79/1.00  --gc_record_bc_elim                     false
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing Options
% 3.79/1.00  
% 3.79/1.00  --preprocessing_flag                    true
% 3.79/1.00  --time_out_prep_mult                    0.1
% 3.79/1.00  --splitting_mode                        input
% 3.79/1.00  --splitting_grd                         true
% 3.79/1.00  --splitting_cvd                         false
% 3.79/1.00  --splitting_cvd_svl                     false
% 3.79/1.00  --splitting_nvd                         32
% 3.79/1.00  --sub_typing                            true
% 3.79/1.00  --prep_gs_sim                           true
% 3.79/1.00  --prep_unflatten                        true
% 3.79/1.00  --prep_res_sim                          true
% 3.79/1.00  --prep_upred                            true
% 3.79/1.00  --prep_sem_filter                       exhaustive
% 3.79/1.00  --prep_sem_filter_out                   false
% 3.79/1.00  --pred_elim                             true
% 3.79/1.00  --res_sim_input                         true
% 3.79/1.00  --eq_ax_congr_red                       true
% 3.79/1.00  --pure_diseq_elim                       true
% 3.79/1.00  --brand_transform                       false
% 3.79/1.00  --non_eq_to_eq                          false
% 3.79/1.00  --prep_def_merge                        true
% 3.79/1.00  --prep_def_merge_prop_impl              false
% 3.79/1.00  --prep_def_merge_mbd                    true
% 3.79/1.00  --prep_def_merge_tr_red                 false
% 3.79/1.00  --prep_def_merge_tr_cl                  false
% 3.79/1.00  --smt_preprocessing                     true
% 3.79/1.00  --smt_ac_axioms                         fast
% 3.79/1.00  --preprocessed_out                      false
% 3.79/1.00  --preprocessed_stats                    false
% 3.79/1.00  
% 3.79/1.00  ------ Abstraction refinement Options
% 3.79/1.00  
% 3.79/1.00  --abstr_ref                             []
% 3.79/1.00  --abstr_ref_prep                        false
% 3.79/1.00  --abstr_ref_until_sat                   false
% 3.79/1.00  --abstr_ref_sig_restrict                funpre
% 3.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.00  --abstr_ref_under                       []
% 3.79/1.00  
% 3.79/1.00  ------ SAT Options
% 3.79/1.00  
% 3.79/1.00  --sat_mode                              false
% 3.79/1.00  --sat_fm_restart_options                ""
% 3.79/1.00  --sat_gr_def                            false
% 3.79/1.00  --sat_epr_types                         true
% 3.79/1.00  --sat_non_cyclic_types                  false
% 3.79/1.00  --sat_finite_models                     false
% 3.79/1.00  --sat_fm_lemmas                         false
% 3.79/1.00  --sat_fm_prep                           false
% 3.79/1.00  --sat_fm_uc_incr                        true
% 3.79/1.00  --sat_out_model                         small
% 3.79/1.00  --sat_out_clauses                       false
% 3.79/1.00  
% 3.79/1.00  ------ QBF Options
% 3.79/1.00  
% 3.79/1.00  --qbf_mode                              false
% 3.79/1.00  --qbf_elim_univ                         false
% 3.79/1.00  --qbf_dom_inst                          none
% 3.79/1.00  --qbf_dom_pre_inst                      false
% 3.79/1.00  --qbf_sk_in                             false
% 3.79/1.00  --qbf_pred_elim                         true
% 3.79/1.00  --qbf_split                             512
% 3.79/1.00  
% 3.79/1.00  ------ BMC1 Options
% 3.79/1.00  
% 3.79/1.00  --bmc1_incremental                      false
% 3.79/1.00  --bmc1_axioms                           reachable_all
% 3.79/1.00  --bmc1_min_bound                        0
% 3.79/1.00  --bmc1_max_bound                        -1
% 3.79/1.00  --bmc1_max_bound_default                -1
% 3.79/1.00  --bmc1_symbol_reachability              true
% 3.79/1.00  --bmc1_property_lemmas                  false
% 3.79/1.00  --bmc1_k_induction                      false
% 3.79/1.00  --bmc1_non_equiv_states                 false
% 3.79/1.00  --bmc1_deadlock                         false
% 3.79/1.00  --bmc1_ucm                              false
% 3.79/1.00  --bmc1_add_unsat_core                   none
% 3.79/1.00  --bmc1_unsat_core_children              false
% 3.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.00  --bmc1_out_stat                         full
% 3.79/1.00  --bmc1_ground_init                      false
% 3.79/1.00  --bmc1_pre_inst_next_state              false
% 3.79/1.00  --bmc1_pre_inst_state                   false
% 3.79/1.00  --bmc1_pre_inst_reach_state             false
% 3.79/1.00  --bmc1_out_unsat_core                   false
% 3.79/1.00  --bmc1_aig_witness_out                  false
% 3.79/1.00  --bmc1_verbose                          false
% 3.79/1.00  --bmc1_dump_clauses_tptp                false
% 3.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.00  --bmc1_dump_file                        -
% 3.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.00  --bmc1_ucm_extend_mode                  1
% 3.79/1.00  --bmc1_ucm_init_mode                    2
% 3.79/1.00  --bmc1_ucm_cone_mode                    none
% 3.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.00  --bmc1_ucm_relax_model                  4
% 3.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.00  --bmc1_ucm_layered_model                none
% 3.79/1.00  --bmc1_ucm_max_lemma_size               10
% 3.79/1.00  
% 3.79/1.00  ------ AIG Options
% 3.79/1.00  
% 3.79/1.00  --aig_mode                              false
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation Options
% 3.79/1.00  
% 3.79/1.00  --instantiation_flag                    true
% 3.79/1.00  --inst_sos_flag                         false
% 3.79/1.00  --inst_sos_phase                        true
% 3.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.00  --inst_lit_sel_side                     none
% 3.79/1.00  --inst_solver_per_active                1400
% 3.79/1.00  --inst_solver_calls_frac                1.
% 3.79/1.00  --inst_passive_queue_type               priority_queues
% 3.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.00  --inst_passive_queues_freq              [25;2]
% 3.79/1.00  --inst_dismatching                      true
% 3.79/1.00  --inst_eager_unprocessed_to_passive     true
% 3.79/1.00  --inst_prop_sim_given                   true
% 3.79/1.00  --inst_prop_sim_new                     false
% 3.79/1.00  --inst_subs_new                         false
% 3.79/1.00  --inst_eq_res_simp                      false
% 3.79/1.00  --inst_subs_given                       false
% 3.79/1.00  --inst_orphan_elimination               true
% 3.79/1.00  --inst_learning_loop_flag               true
% 3.79/1.00  --inst_learning_start                   3000
% 3.79/1.00  --inst_learning_factor                  2
% 3.79/1.00  --inst_start_prop_sim_after_learn       3
% 3.79/1.00  --inst_sel_renew                        solver
% 3.79/1.00  --inst_lit_activity_flag                true
% 3.79/1.00  --inst_restr_to_given                   false
% 3.79/1.00  --inst_activity_threshold               500
% 3.79/1.00  --inst_out_proof                        true
% 3.79/1.00  
% 3.79/1.00  ------ Resolution Options
% 3.79/1.00  
% 3.79/1.00  --resolution_flag                       false
% 3.79/1.00  --res_lit_sel                           adaptive
% 3.79/1.00  --res_lit_sel_side                      none
% 3.79/1.00  --res_ordering                          kbo
% 3.79/1.00  --res_to_prop_solver                    active
% 3.79/1.00  --res_prop_simpl_new                    false
% 3.79/1.00  --res_prop_simpl_given                  true
% 3.79/1.00  --res_passive_queue_type                priority_queues
% 3.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.00  --res_passive_queues_freq               [15;5]
% 3.79/1.00  --res_forward_subs                      full
% 3.79/1.00  --res_backward_subs                     full
% 3.79/1.00  --res_forward_subs_resolution           true
% 3.79/1.00  --res_backward_subs_resolution          true
% 3.79/1.00  --res_orphan_elimination                true
% 3.79/1.00  --res_time_limit                        2.
% 3.79/1.00  --res_out_proof                         true
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Options
% 3.79/1.00  
% 3.79/1.00  --superposition_flag                    true
% 3.79/1.00  --sup_passive_queue_type                priority_queues
% 3.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.00  --demod_completeness_check              fast
% 3.79/1.00  --demod_use_ground                      true
% 3.79/1.00  --sup_to_prop_solver                    passive
% 3.79/1.00  --sup_prop_simpl_new                    true
% 3.79/1.00  --sup_prop_simpl_given                  true
% 3.79/1.00  --sup_fun_splitting                     false
% 3.79/1.00  --sup_smt_interval                      50000
% 3.79/1.00  
% 3.79/1.00  ------ Superposition Simplification Setup
% 3.79/1.00  
% 3.79/1.00  --sup_indices_passive                   []
% 3.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_full_bw                           [BwDemod]
% 3.79/1.00  --sup_immed_triv                        [TrivRules]
% 3.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_immed_bw_main                     []
% 3.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.00  
% 3.79/1.00  ------ Combination Options
% 3.79/1.00  
% 3.79/1.00  --comb_res_mult                         3
% 3.79/1.00  --comb_sup_mult                         2
% 3.79/1.00  --comb_inst_mult                        10
% 3.79/1.00  
% 3.79/1.00  ------ Debug Options
% 3.79/1.00  
% 3.79/1.00  --dbg_backtrace                         false
% 3.79/1.00  --dbg_dump_prop_clauses                 false
% 3.79/1.00  --dbg_dump_prop_clauses_file            -
% 3.79/1.00  --dbg_out_stat                          false
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ Proving...
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS status Theorem for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  fof(f18,conjecture,(
% 3.79/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f19,negated_conjecture,(
% 3.79/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.79/1.00    inference(negated_conjecture,[],[f18])).
% 3.79/1.00  
% 3.79/1.00  fof(f39,plain,(
% 3.79/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.79/1.00    inference(ennf_transformation,[],[f19])).
% 3.79/1.00  
% 3.79/1.00  fof(f40,plain,(
% 3.79/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.79/1.00    inference(flattening,[],[f39])).
% 3.79/1.00  
% 3.79/1.00  fof(f56,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f55,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f54,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f53,plain,(
% 3.79/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f57,plain,(
% 3.79/1.00    (((k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f40,f56,f55,f54,f53])).
% 3.79/1.00  
% 3.79/1.00  fof(f95,plain,(
% 3.79/1.00    m1_subset_1(sK7,sK3)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f7,axiom,(
% 3.79/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f23,plain,(
% 3.79/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.79/1.00    inference(ennf_transformation,[],[f7])).
% 3.79/1.00  
% 3.79/1.00  fof(f24,plain,(
% 3.79/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.79/1.00    inference(flattening,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f71,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f24])).
% 3.79/1.00  
% 3.79/1.00  fof(f97,plain,(
% 3.79/1.00    k1_xboole_0 != sK3),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f5,axiom,(
% 3.79/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f51,plain,(
% 3.79/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.79/1.00    inference(nnf_transformation,[],[f5])).
% 3.79/1.00  
% 3.79/1.00  fof(f52,plain,(
% 3.79/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.79/1.00    inference(flattening,[],[f51])).
% 3.79/1.00  
% 3.79/1.00  fof(f67,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f52])).
% 3.79/1.00  
% 3.79/1.00  fof(f68,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f52])).
% 3.79/1.00  
% 3.79/1.00  fof(f102,plain,(
% 3.79/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.79/1.00    inference(equality_resolution,[],[f68])).
% 3.79/1.00  
% 3.79/1.00  fof(f3,axiom,(
% 3.79/1.00    v1_xboole_0(k1_xboole_0)),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f63,plain,(
% 3.79/1.00    v1_xboole_0(k1_xboole_0)),
% 3.79/1.00    inference(cnf_transformation,[],[f3])).
% 3.79/1.00  
% 3.79/1.00  fof(f2,axiom,(
% 3.79/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f21,plain,(
% 3.79/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.79/1.00    inference(ennf_transformation,[],[f2])).
% 3.79/1.00  
% 3.79/1.00  fof(f45,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/1.00    inference(nnf_transformation,[],[f21])).
% 3.79/1.00  
% 3.79/1.00  fof(f46,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/1.00    inference(rectify,[],[f45])).
% 3.79/1.00  
% 3.79/1.00  fof(f47,plain,(
% 3.79/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f48,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.79/1.00  
% 3.79/1.00  fof(f61,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f48])).
% 3.79/1.00  
% 3.79/1.00  fof(f4,axiom,(
% 3.79/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f49,plain,(
% 3.79/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/1.00    inference(nnf_transformation,[],[f4])).
% 3.79/1.00  
% 3.79/1.00  fof(f50,plain,(
% 3.79/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/1.00    inference(flattening,[],[f49])).
% 3.79/1.00  
% 3.79/1.00  fof(f66,plain,(
% 3.79/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f50])).
% 3.79/1.00  
% 3.79/1.00  fof(f1,axiom,(
% 3.79/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f41,plain,(
% 3.79/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.79/1.00    inference(nnf_transformation,[],[f1])).
% 3.79/1.00  
% 3.79/1.00  fof(f42,plain,(
% 3.79/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.79/1.00    inference(rectify,[],[f41])).
% 3.79/1.00  
% 3.79/1.00  fof(f43,plain,(
% 3.79/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f44,plain,(
% 3.79/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.79/1.00  
% 3.79/1.00  fof(f58,plain,(
% 3.79/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f44])).
% 3.79/1.00  
% 3.79/1.00  fof(f94,plain,(
% 3.79/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f12,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f28,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.00    inference(ennf_transformation,[],[f12])).
% 3.79/1.00  
% 3.79/1.00  fof(f76,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f28])).
% 3.79/1.00  
% 3.79/1.00  fof(f96,plain,(
% 3.79/1.00    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f92,plain,(
% 3.79/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f17,axiom,(
% 3.79/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f37,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.79/1.00    inference(ennf_transformation,[],[f17])).
% 3.79/1.00  
% 3.79/1.00  fof(f38,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.79/1.00    inference(flattening,[],[f37])).
% 3.79/1.00  
% 3.79/1.00  fof(f87,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f38])).
% 3.79/1.00  
% 3.79/1.00  fof(f89,plain,(
% 3.79/1.00    ~v1_xboole_0(sK4)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f90,plain,(
% 3.79/1.00    v1_funct_1(sK5)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f91,plain,(
% 3.79/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f16,axiom,(
% 3.79/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f35,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.79/1.00    inference(ennf_transformation,[],[f16])).
% 3.79/1.00  
% 3.79/1.00  fof(f36,plain,(
% 3.79/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.79/1.00    inference(flattening,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f82,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f85,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f38])).
% 3.79/1.00  
% 3.79/1.00  fof(f11,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f20,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.79/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.79/1.00  
% 3.79/1.00  fof(f27,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/1.00    inference(ennf_transformation,[],[f20])).
% 3.79/1.00  
% 3.79/1.00  fof(f75,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f27])).
% 3.79/1.00  
% 3.79/1.00  fof(f14,axiom,(
% 3.79/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f31,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.79/1.00    inference(ennf_transformation,[],[f14])).
% 3.79/1.00  
% 3.79/1.00  fof(f32,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.79/1.00    inference(flattening,[],[f31])).
% 3.79/1.00  
% 3.79/1.00  fof(f80,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f32])).
% 3.79/1.00  
% 3.79/1.00  fof(f93,plain,(
% 3.79/1.00    v1_funct_1(sK6)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f8,axiom,(
% 3.79/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f25,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f8])).
% 3.79/1.00  
% 3.79/1.00  fof(f72,plain,(
% 3.79/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f25])).
% 3.79/1.00  
% 3.79/1.00  fof(f9,axiom,(
% 3.79/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f73,plain,(
% 3.79/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f9])).
% 3.79/1.00  
% 3.79/1.00  fof(f15,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f33,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.79/1.00    inference(ennf_transformation,[],[f15])).
% 3.79/1.00  
% 3.79/1.00  fof(f34,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.79/1.00    inference(flattening,[],[f33])).
% 3.79/1.00  
% 3.79/1.00  fof(f81,plain,(
% 3.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f34])).
% 3.79/1.00  
% 3.79/1.00  fof(f98,plain,(
% 3.79/1.00    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 3.79/1.00    inference(cnf_transformation,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  fof(f6,axiom,(
% 3.79/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f22,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f6])).
% 3.79/1.00  
% 3.79/1.00  fof(f70,plain,(
% 3.79/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f22])).
% 3.79/1.00  
% 3.79/1.00  fof(f13,axiom,(
% 3.79/1.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f29,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.79/1.00    inference(ennf_transformation,[],[f13])).
% 3.79/1.00  
% 3.79/1.00  fof(f30,plain,(
% 3.79/1.00    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.79/1.00    inference(flattening,[],[f29])).
% 3.79/1.00  
% 3.79/1.00  fof(f78,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f30])).
% 3.79/1.00  
% 3.79/1.00  fof(f10,axiom,(
% 3.79/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f26,plain,(
% 3.79/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f10])).
% 3.79/1.00  
% 3.79/1.00  fof(f74,plain,(
% 3.79/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f69,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.79/1.00    inference(cnf_transformation,[],[f52])).
% 3.79/1.00  
% 3.79/1.00  fof(f101,plain,(
% 3.79/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.79/1.00    inference(equality_resolution,[],[f69])).
% 3.79/1.00  
% 3.79/1.00  cnf(c_34,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK7,sK3) ),
% 3.79/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1150,plain,
% 3.79/1.00      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_13,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1162,plain,
% 3.79/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.79/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.79/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3808,plain,
% 3.79/1.00      ( r2_hidden(sK7,sK3) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1150,c_1162]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_32,negated_conjecture,
% 3.79/1.00      ( k1_xboole_0 != sK3 ),
% 3.79/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_11,plain,
% 3.79/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = X1
% 3.79/1.00      | k1_xboole_0 = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_84,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_85,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5,plain,
% 3.79/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_93,plain,
% 3.79/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_588,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1463,plain,
% 3.79/1.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_588]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1464,plain,
% 3.79/1.00      ( sK3 != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = sK3
% 3.79/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3,plain,
% 3.79/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1566,plain,
% 3.79/1.00      ( r1_tarski(sK3,k1_xboole_0)
% 3.79/1.00      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1567,plain,
% 3.79/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.79/1.00      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6,plain,
% 3.79/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1605,plain,
% 3.79/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1606,plain,
% 3.79/1.00      ( sK3 = X0
% 3.79/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.79/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1605]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1608,plain,
% 3.79/1.00      ( sK3 = k1_xboole_0
% 3.79/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.79/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1606]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1788,plain,
% 3.79/1.00      ( r1_tarski(k1_xboole_0,sK3)
% 3.79/1.00      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1789,plain,
% 3.79/1.00      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 3.79/1.00      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2228,plain,
% 3.79/1.00      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2229,plain,
% 3.79/1.00      ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2228]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4020,plain,
% 3.79/1.00      ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
% 3.79/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4021,plain,
% 3.79/1.00      ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
% 3.79/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_4020]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4192,plain,
% 3.79/1.00      ( r2_hidden(sK7,sK3) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_3808,c_32,c_84,c_85,c_93,c_1464,c_1567,c_1608,c_1789,
% 3.79/1.00                 c_2229,c_4021]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_35,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1149,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_18,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1158,plain,
% 3.79/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2780,plain,
% 3.79/1.00      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1149,c_1158]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_33,negated_conjecture,
% 3.79/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1151,plain,
% 3.79/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3162,plain,
% 3.79/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_2780,c_1151]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_37,negated_conjecture,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1147,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_26,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.79/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | k1_xboole_0 = X2 ),
% 3.79/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1154,plain,
% 3.79/1.00      ( k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3768,plain,
% 3.79/1.00      ( sK4 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.79/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1147,c_1154]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_40,negated_conjecture,
% 3.79/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.79/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_39,negated_conjecture,
% 3.79/1.00      ( v1_funct_1(sK5) ),
% 3.79/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_42,plain,
% 3.79/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_38,negated_conjecture,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.79/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_43,plain,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_589,plain,
% 3.79/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.79/1.00      theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1436,plain,
% 3.79/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_589]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1438,plain,
% 3.79/1.00      ( v1_xboole_0(sK4)
% 3.79/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.79/1.00      | sK4 != k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4924,plain,
% 3.79/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.79/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_3768,c_40,c_42,c_43,c_44,c_5,c_1438,c_1748,c_2173,
% 3.79/1.00                 c_2594]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4925,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_4924]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4933,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3162,c_4925]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_24,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ r2_hidden(X3,X1)
% 3.79/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | k1_xboole_0 = X2 ),
% 3.79/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1156,plain,
% 3.79/1.00      ( k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.79/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.79/1.00      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5011,plain,
% 3.79/1.00      ( k1_relat_1(sK6) = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.79/1.00      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4933,c_1156]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_28,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | v1_funct_2(X0,X1,X3)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | k1_xboole_0 = X2 ),
% 3.79/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1152,plain,
% 3.79/1.00      ( k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.79/1.00      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2613,plain,
% 3.79/1.00      ( sK4 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1147,c_1152]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3625,plain,
% 3.79/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.79/1.00      | v1_funct_2(sK5,sK3,X0) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_2613,c_40,c_42,c_43,c_5,c_1438]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3626,plain,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_3625]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3634,plain,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3162,c_3626]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10858,plain,
% 3.79/1.00      ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.79/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.79/1.00      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5011,c_42,c_3634]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10859,plain,
% 3.79/1.00      ( k1_relat_1(sK6) = k1_xboole_0
% 3.79/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.79/1.00      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_10858]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_17,plain,
% 3.79/1.00      ( v5_relat_1(X0,X1)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_22,plain,
% 3.79/1.00      ( ~ v5_relat_1(X0,X1)
% 3.79/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_357,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_17,c_22]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1142,plain,
% 3.79/1.00      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.79/1.00      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1760,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.79/1.00      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1149,c_1142]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_36,negated_conjecture,
% 3.79/1.00      ( v1_funct_1(sK6) ),
% 3.79/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_45,plain,
% 3.79/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1948,plain,
% 3.79/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.79/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_1760,c_45]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1949,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.79/1.00      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_1948]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10869,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.79/1.00      | k1_relat_1(sK6) = k1_xboole_0
% 3.79/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_10859,c_1949]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_46,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_14,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/1.00      | ~ v1_relat_1(X1)
% 3.79/1.00      | v1_relat_1(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1431,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | v1_relat_1(X0)
% 3.79/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1810,plain,
% 3.79/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.79/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
% 3.79/1.00      | v1_relat_1(sK6) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1431]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1811,plain,
% 3.79/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.79/1.00      | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 3.79/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_15,plain,
% 3.79/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2555,plain,
% 3.79/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2556,plain,
% 3.79/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2555]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10909,plain,
% 3.79/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.79/1.00      | k1_relat_1(sK6) = k1_xboole_0
% 3.79/1.00      | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_10869,c_46,c_1811,c_2556]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10910,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.79/1.00      | k1_relat_1(sK6) = k1_xboole_0
% 3.79/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_10909]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10920,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 3.79/1.00      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4192,c_10910]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_23,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X3,X1)
% 3.79/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.79/1.00      | ~ v1_funct_1(X4)
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | v1_xboole_0(X2)
% 3.79/1.00      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.79/1.00      | k1_xboole_0 = X1 ),
% 3.79/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1157,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.79/1.00      | k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.79/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.79/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.79/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.79/1.00      | v1_funct_1(X3) != iProver_top
% 3.79/1.00      | v1_funct_1(X4) != iProver_top
% 3.79/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5201,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 3.79/1.00      | k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X1,X0,sK4) != iProver_top
% 3.79/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top
% 3.79/1.00      | v1_funct_1(sK6) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2780,c_1157]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_41,plain,
% 3.79/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5912,plain,
% 3.79/1.00      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 3.79/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.79/1.00      | v1_funct_2(X1,X0,sK4) != iProver_top
% 3.79/1.00      | k1_xboole_0 = X0
% 3.79/1.00      | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 3.79/1.00      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5201,c_41,c_45,c_46]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5913,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 3.79/1.00      | k1_xboole_0 = X0
% 3.79/1.00      | v1_funct_2(X1,X0,sK4) != iProver_top
% 3.79/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 3.79/1.00      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 3.79/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_5912]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5923,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.79/1.00      | sK3 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,sK3) != iProver_top
% 3.79/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.79/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3162,c_5913]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_44,plain,
% 3.79/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5928,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.79/1.00      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5923,c_42,c_43,c_44,c_32,c_84,c_85,c_1464]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5936,plain,
% 3.79/1.00      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1150,c_5928]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_31,negated_conjecture,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 3.79/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6196,plain,
% 3.79/1.00      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_5936,c_31]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_11002,plain,
% 3.79/1.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_10920,c_6196]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_12,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/1.00      | ~ v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1163,plain,
% 3.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.79/1.00      | v1_xboole_0(X1) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5007,plain,
% 3.79/1.00      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4933,c_1163]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_20,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_1(X0)
% 3.79/1.00      | ~ v1_xboole_0(X0)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_16,plain,
% 3.79/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_189,plain,
% 3.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_xboole_0(X0)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X2) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_20,c_16]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_190,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | ~ v1_xboole_0(X0)
% 3.79/1.00      | v1_xboole_0(X1)
% 3.79/1.00      | v1_xboole_0(X2) ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_189]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1143,plain,
% 3.79/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.79/1.00      | v1_xboole_0(X0) != iProver_top
% 3.79/1.00      | v1_xboole_0(X2) = iProver_top
% 3.79/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2103,plain,
% 3.79/1.00      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.79/1.00      | v1_xboole_0(sK4) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK3) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1147,c_1143]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2390,plain,
% 3.79/1.00      ( v1_xboole_0(sK3) = iProver_top
% 3.79/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_2103,c_41,c_43]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6190,plain,
% 3.79/1.00      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_relat_1(sK6))) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5007,c_41,c_43,c_32,c_84,c_85,c_93,c_1464,c_1567,
% 3.79/1.00                 c_1608,c_1789,c_2103,c_2229,c_4021]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_11022,plain,
% 3.79/1.00      ( v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_11002,c_6190]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9,plain,
% 3.79/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_11080,plain,
% 3.79/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_11022,c_9]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(contradiction,plain,
% 3.79/1.00      ( $false ),
% 3.79/1.00      inference(minisat,[status(thm)],[c_11080,c_93]) ).
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  ------                               Statistics
% 3.79/1.00  
% 3.79/1.00  ------ General
% 3.79/1.00  
% 3.79/1.00  abstr_ref_over_cycles:                  0
% 3.79/1.00  abstr_ref_under_cycles:                 0
% 3.79/1.00  gc_basic_clause_elim:                   0
% 3.79/1.00  forced_gc_time:                         0
% 3.79/1.00  parsing_time:                           0.011
% 3.79/1.00  unif_index_cands_time:                  0.
% 3.79/1.00  unif_index_add_time:                    0.
% 3.79/1.00  orderings_time:                         0.
% 3.79/1.00  out_proof_time:                         0.011
% 3.79/1.00  total_time:                             0.347
% 3.79/1.00  num_of_symbols:                         56
% 3.79/1.00  num_of_terms:                           12292
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing
% 3.79/1.00  
% 3.79/1.00  num_of_splits:                          0
% 3.79/1.00  num_of_split_atoms:                     0
% 3.79/1.00  num_of_reused_defs:                     0
% 3.79/1.00  num_eq_ax_congr_red:                    14
% 3.79/1.00  num_of_sem_filtered_clauses:            1
% 3.79/1.00  num_of_subtypes:                        0
% 3.79/1.00  monotx_restored_types:                  0
% 3.79/1.00  sat_num_of_epr_types:                   0
% 3.79/1.00  sat_num_of_non_cyclic_types:            0
% 3.79/1.00  sat_guarded_non_collapsed_types:        0
% 3.79/1.00  num_pure_diseq_elim:                    0
% 3.79/1.00  simp_replaced_by:                       0
% 3.79/1.00  res_preprocessed:                       174
% 3.79/1.00  prep_upred:                             0
% 3.79/1.00  prep_unflattend:                        0
% 3.79/1.00  smt_new_axioms:                         0
% 3.79/1.00  pred_elim_cands:                        7
% 3.79/1.00  pred_elim:                              1
% 3.79/1.00  pred_elim_cl:                           1
% 3.79/1.00  pred_elim_cycles:                       3
% 3.79/1.00  merged_defs:                            0
% 3.79/1.00  merged_defs_ncl:                        0
% 3.79/1.00  bin_hyper_res:                          0
% 3.79/1.00  prep_cycles:                            4
% 3.79/1.00  pred_elim_time:                         0.002
% 3.79/1.00  splitting_time:                         0.
% 3.79/1.00  sem_filter_time:                        0.
% 3.79/1.00  monotx_time:                            0.001
% 3.79/1.00  subtype_inf_time:                       0.
% 3.79/1.00  
% 3.79/1.00  ------ Problem properties
% 3.79/1.00  
% 3.79/1.00  clauses:                                35
% 3.79/1.00  conjectures:                            10
% 3.79/1.00  epr:                                    13
% 3.79/1.00  horn:                                   26
% 3.79/1.00  ground:                                 11
% 3.79/1.00  unary:                                  15
% 3.79/1.00  binary:                                 6
% 3.79/1.00  lits:                                   93
% 3.79/1.00  lits_eq:                                15
% 3.79/1.00  fd_pure:                                0
% 3.79/1.00  fd_pseudo:                              0
% 3.79/1.00  fd_cond:                                5
% 3.79/1.00  fd_pseudo_cond:                         1
% 3.79/1.00  ac_symbols:                             0
% 3.79/1.00  
% 3.79/1.00  ------ Propositional Solver
% 3.79/1.00  
% 3.79/1.00  prop_solver_calls:                      28
% 3.79/1.00  prop_fast_solver_calls:                 1538
% 3.79/1.00  smt_solver_calls:                       0
% 3.79/1.00  smt_fast_solver_calls:                  0
% 3.79/1.00  prop_num_of_clauses:                    4175
% 3.79/1.00  prop_preprocess_simplified:             10681
% 3.79/1.00  prop_fo_subsumed:                       69
% 3.79/1.00  prop_solver_time:                       0.
% 3.79/1.00  smt_solver_time:                        0.
% 3.79/1.00  smt_fast_solver_time:                   0.
% 3.79/1.00  prop_fast_solver_time:                  0.
% 3.79/1.00  prop_unsat_core_time:                   0.
% 3.79/1.00  
% 3.79/1.00  ------ QBF
% 3.79/1.00  
% 3.79/1.00  qbf_q_res:                              0
% 3.79/1.00  qbf_num_tautologies:                    0
% 3.79/1.00  qbf_prep_cycles:                        0
% 3.79/1.00  
% 3.79/1.00  ------ BMC1
% 3.79/1.00  
% 3.79/1.00  bmc1_current_bound:                     -1
% 3.79/1.00  bmc1_last_solved_bound:                 -1
% 3.79/1.00  bmc1_unsat_core_size:                   -1
% 3.79/1.00  bmc1_unsat_core_parents_size:           -1
% 3.79/1.00  bmc1_merge_next_fun:                    0
% 3.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation
% 3.79/1.00  
% 3.79/1.00  inst_num_of_clauses:                    1397
% 3.79/1.00  inst_num_in_passive:                    314
% 3.79/1.00  inst_num_in_active:                     570
% 3.79/1.00  inst_num_in_unprocessed:                513
% 3.79/1.00  inst_num_of_loops:                      720
% 3.79/1.00  inst_num_of_learning_restarts:          0
% 3.79/1.00  inst_num_moves_active_passive:          146
% 3.79/1.00  inst_lit_activity:                      0
% 3.79/1.00  inst_lit_activity_moves:                0
% 3.79/1.00  inst_num_tautologies:                   0
% 3.79/1.00  inst_num_prop_implied:                  0
% 3.79/1.00  inst_num_existing_simplified:           0
% 3.79/1.00  inst_num_eq_res_simplified:             0
% 3.79/1.00  inst_num_child_elim:                    0
% 3.79/1.00  inst_num_of_dismatching_blockings:      264
% 3.79/1.00  inst_num_of_non_proper_insts:           1104
% 3.79/1.00  inst_num_of_duplicates:                 0
% 3.79/1.00  inst_inst_num_from_inst_to_res:         0
% 3.79/1.00  inst_dismatching_checking_time:         0.
% 3.79/1.00  
% 3.79/1.00  ------ Resolution
% 3.79/1.00  
% 3.79/1.00  res_num_of_clauses:                     0
% 3.79/1.00  res_num_in_passive:                     0
% 3.79/1.00  res_num_in_active:                      0
% 3.79/1.00  res_num_of_loops:                       178
% 3.79/1.00  res_forward_subset_subsumed:            145
% 3.79/1.00  res_backward_subset_subsumed:           6
% 3.79/1.00  res_forward_subsumed:                   0
% 3.79/1.00  res_backward_subsumed:                  0
% 3.79/1.00  res_forward_subsumption_resolution:     0
% 3.79/1.00  res_backward_subsumption_resolution:    0
% 3.79/1.00  res_clause_to_clause_subsumption:       526
% 3.79/1.00  res_orphan_elimination:                 0
% 3.79/1.00  res_tautology_del:                      55
% 3.79/1.00  res_num_eq_res_simplified:              0
% 3.79/1.00  res_num_sel_changes:                    0
% 3.79/1.00  res_moves_from_active_to_pass:          0
% 3.79/1.00  
% 3.79/1.00  ------ Superposition
% 3.79/1.00  
% 3.79/1.00  sup_time_total:                         0.
% 3.79/1.00  sup_time_generating:                    0.
% 3.79/1.00  sup_time_sim_full:                      0.
% 3.79/1.00  sup_time_sim_immed:                     0.
% 3.79/1.00  
% 3.79/1.00  sup_num_of_clauses:                     190
% 3.79/1.00  sup_num_in_active:                      105
% 3.79/1.00  sup_num_in_passive:                     85
% 3.79/1.00  sup_num_of_loops:                       142
% 3.79/1.00  sup_fw_superposition:                   111
% 3.79/1.00  sup_bw_superposition:                   137
% 3.79/1.00  sup_immediate_simplified:               27
% 3.79/1.00  sup_given_eliminated:                   0
% 3.79/1.00  comparisons_done:                       0
% 3.79/1.00  comparisons_avoided:                    30
% 3.79/1.00  
% 3.79/1.00  ------ Simplifications
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  sim_fw_subset_subsumed:                 21
% 3.79/1.00  sim_bw_subset_subsumed:                 20
% 3.79/1.00  sim_fw_subsumed:                        8
% 3.79/1.00  sim_bw_subsumed:                        0
% 3.79/1.00  sim_fw_subsumption_res:                 0
% 3.79/1.00  sim_bw_subsumption_res:                 0
% 3.79/1.00  sim_tautology_del:                      8
% 3.79/1.00  sim_eq_tautology_del:                   12
% 3.79/1.00  sim_eq_res_simp:                        0
% 3.79/1.00  sim_fw_demodulated:                     7
% 3.79/1.00  sim_bw_demodulated:                     31
% 3.79/1.00  sim_light_normalised:                   0
% 3.79/1.00  sim_joinable_taut:                      0
% 3.79/1.00  sim_joinable_simp:                      0
% 3.79/1.00  sim_ac_normalised:                      0
% 3.79/1.00  sim_smt_subsumption:                    0
% 3.79/1.00  
%------------------------------------------------------------------------------
