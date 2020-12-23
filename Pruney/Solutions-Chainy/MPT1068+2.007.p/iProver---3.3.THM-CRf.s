%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:36 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  245 (2063 expanded)
%              Number of clauses        :  155 ( 608 expanded)
%              Number of leaves         :   25 ( 660 expanded)
%              Depth                    :   24
%              Number of atoms          :  834 (15076 expanded)
%              Number of equality atoms :  383 (4267 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f48])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f49,f62,f61,f60,f59])).

fof(f104,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f95])).

fof(f113,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f105,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3069,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3043,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3062,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5088,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3043,c_3062])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3124,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3125,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3124])).

cnf(c_3212,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3428,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | r2_hidden(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_3429,plain,
    ( m1_subset_1(sK6,sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3428])).

cnf(c_5444,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5088,c_50,c_35,c_3125,c_3429])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3061,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3059,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6060,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3061,c_3059])).

cnf(c_12978,plain,
    ( m1_subset_1(sK6,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5444,c_6060])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_26,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_922,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | X3 != X1
    | k1_xboole_0 != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_923,plain,
    ( v1_partfun1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_937,plain,
    ( v1_partfun1(k1_xboole_0,X0)
    | ~ v1_funct_1(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_923,c_9])).

cnf(c_942,plain,
    ( k1_xboole_0 = X0
    | v1_partfun1(k1_xboole_0,X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1095,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_1096,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1097,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3129,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3130,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3129])).

cnf(c_2207,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3157,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_3163,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3157])).

cnf(c_3165,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3163])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3456,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3455])).

cnf(c_3458,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_3246,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3464,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3246])).

cnf(c_2208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3232,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_3490,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_3491,plain,
    ( sK2 != sK2
    | k1_xboole_0 != X0
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3490])).

cnf(c_2213,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3621,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_3622,plain,
    ( X0 != sK4
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3621])).

cnf(c_3624,plain,
    ( k1_xboole_0 != sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3622])).

cnf(c_3810,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3132,plain,
    ( ~ v1_funct_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4341,plain,
    ( ~ v1_funct_2(sK4,sK2,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_3132])).

cnf(c_4344,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK4
    | v1_funct_2(sK4,sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4341])).

cnf(c_4513,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4514,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4513])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4468,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6664,plain,
    ( v1_funct_2(sK4,sK2,X0)
    | ~ v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4468])).

cnf(c_6665,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | v1_partfun1(sK4,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6664])).

cnf(c_6667,plain,
    ( v1_funct_2(sK4,sK2,k1_xboole_0) = iProver_top
    | v1_partfun1(sK4,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6665])).

cnf(c_9578,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9579,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9578])).

cnf(c_9581,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9579])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3041,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3040,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3047,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6839,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_3047])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3056,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5006,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3040,c_3056])).

cnf(c_6840,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6839,c_5006])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8527,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6840,c_46])).

cnf(c_8528,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8527])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3058,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8529,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | sK3 = k1_xboole_0
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8528,c_3058])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3057,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4493,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_3057])).

cnf(c_11711,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | sK3 = k1_xboole_0
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8529,c_45,c_4493])).

cnf(c_11712,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | sK3 = k1_xboole_0
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11711])).

cnf(c_11718,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
    | sK3 = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5444,c_11712])).

cnf(c_11738,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3041,c_11718])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3042,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4492,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3057])).

cnf(c_5005,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3042,c_3056])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3044,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5240,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5005,c_3044])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3053,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8002,plain,
    ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5005,c_3053])).

cnf(c_48,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9736,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8002,c_48,c_49])).

cnf(c_9737,plain,
    ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9736])).

cnf(c_9742,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5240,c_9737])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3046,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5717,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3046])).

cnf(c_6535,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5717,c_48])).

cnf(c_6536,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6535])).

cnf(c_6544,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_6536])).

cnf(c_6643,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6544,c_45])).

cnf(c_9743,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9742,c_6643])).

cnf(c_9891,plain,
    ( sK3 = k1_xboole_0
    | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9743,c_45,c_46,c_47])).

cnf(c_9892,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9891])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_9893,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9892,c_34])).

cnf(c_11915,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11738,c_4492,c_9893])).

cnf(c_3060,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4066,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_3060])).

cnf(c_11963,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11915,c_4066])).

cnf(c_3063,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3055,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7178,plain,
    ( v1_funct_2(k1_xboole_0,X0,X1) = iProver_top
    | v1_partfun1(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_3055])).

cnf(c_13450,plain,
    ( v1_partfun1(k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k1_xboole_0,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7178,c_44,c_45,c_47,c_35,c_1097,c_3624,c_4344,c_6667,c_9581,c_11963])).

cnf(c_13451,plain,
    ( v1_funct_2(k1_xboole_0,X0,X1) = iProver_top
    | v1_partfun1(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13450])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3045,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4996,plain,
    ( k1_relset_1(X0,X0,k1_xboole_0) = X0
    | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_3045])).

cnf(c_12606,plain,
    ( v1_funct_2(k1_xboole_0,X0,X0) != iProver_top
    | k1_relset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4996,c_44,c_45,c_47,c_35,c_1097,c_3624,c_4344,c_6667,c_9581,c_11963])).

cnf(c_12607,plain,
    ( k1_relset_1(X0,X0,k1_xboole_0) = X0
    | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12606])).

cnf(c_5003,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3063,c_3056])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_544,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_18])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_3035,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_3685,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_3035])).

cnf(c_4064,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_3060])).

cnf(c_3070,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5100,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4064,c_3070])).

cnf(c_8186,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3685,c_5100])).

cnf(c_12612,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12607,c_5003,c_8186])).

cnf(c_13456,plain,
    ( k1_xboole_0 = X0
    | v1_partfun1(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13451,c_12612])).

cnf(c_14483,plain,
    ( r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12978,c_44,c_45,c_47,c_35,c_942,c_1097,c_3130,c_3165,c_3458,c_3464,c_3491,c_3624,c_3810,c_4344,c_4492,c_4514,c_6667,c_9581,c_9893,c_11738,c_11963,c_13456])).

cnf(c_14489,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3069,c_14483])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.99  
% 3.71/0.99  ------  iProver source info
% 3.71/0.99  
% 3.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.99  git: non_committed_changes: false
% 3.71/0.99  git: last_make_outside_of_git: false
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    ""
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             all
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         305.
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              default
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           true
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             true
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         true
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     num_symb
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       true
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     true
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_input_bw                          []
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  ------ Parsing...
% 3.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  ------ Proving...
% 3.71/0.99  ------ Problem Properties 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  clauses                                 39
% 3.71/0.99  conjectures                             10
% 3.71/0.99  EPR                                     11
% 3.71/0.99  Horn                                    31
% 3.71/0.99  unary                                   13
% 3.71/0.99  binary                                  8
% 3.71/0.99  lits                                    100
% 3.71/0.99  lits eq                                 21
% 3.71/0.99  fd_pure                                 0
% 3.71/0.99  fd_pseudo                               0
% 3.71/0.99  fd_cond                                 5
% 3.71/0.99  fd_pseudo_cond                          3
% 3.71/0.99  AC symbols                              0
% 3.71/0.99  
% 3.71/0.99  ------ Schedule dynamic 5 is on 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  Current options:
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    ""
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             all
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         305.
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              default
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           true
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             true
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         true
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     none
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       false
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     true
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_input_bw                          []
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS status Theorem for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99   Resolution empty clause
% 3.71/0.99  
% 3.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  fof(f2,axiom,(
% 3.71/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f50,plain,(
% 3.71/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.99    inference(nnf_transformation,[],[f2])).
% 3.71/0.99  
% 3.71/0.99  fof(f51,plain,(
% 3.71/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.99    inference(flattening,[],[f50])).
% 3.71/0.99  
% 3.71/0.99  fof(f65,plain,(
% 3.71/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.71/0.99    inference(cnf_transformation,[],[f51])).
% 3.71/0.99  
% 3.71/0.99  fof(f109,plain,(
% 3.71/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/0.99    inference(equality_resolution,[],[f65])).
% 3.71/0.99  
% 3.71/0.99  fof(f21,conjecture,(
% 3.71/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f22,negated_conjecture,(
% 3.71/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.71/0.99    inference(negated_conjecture,[],[f21])).
% 3.71/0.99  
% 3.71/0.99  fof(f48,plain,(
% 3.71/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.71/0.99    inference(ennf_transformation,[],[f22])).
% 3.71/0.99  
% 3.71/0.99  fof(f49,plain,(
% 3.71/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.71/0.99    inference(flattening,[],[f48])).
% 3.71/0.99  
% 3.71/0.99  fof(f62,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f61,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f60,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f59,plain,(
% 3.71/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f63,plain,(
% 3.71/0.99    (((k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f49,f62,f61,f60,f59])).
% 3.71/0.99  
% 3.71/0.99  fof(f104,plain,(
% 3.71/0.99    m1_subset_1(sK6,sK2)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f7,axiom,(
% 3.71/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f26,plain,(
% 3.71/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.71/0.99    inference(ennf_transformation,[],[f7])).
% 3.71/0.99  
% 3.71/0.99  fof(f27,plain,(
% 3.71/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.71/0.99    inference(flattening,[],[f26])).
% 3.71/0.99  
% 3.71/0.99  fof(f75,plain,(
% 3.71/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f27])).
% 3.71/0.99  
% 3.71/0.99  fof(f106,plain,(
% 3.71/0.99    k1_xboole_0 != sK2),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f1,axiom,(
% 3.71/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f24,plain,(
% 3.71/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f1])).
% 3.71/0.99  
% 3.71/0.99  fof(f64,plain,(
% 3.71/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f24])).
% 3.71/0.99  
% 3.71/0.99  fof(f8,axiom,(
% 3.71/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f56,plain,(
% 3.71/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.71/0.99    inference(nnf_transformation,[],[f8])).
% 3.71/0.99  
% 3.71/0.99  fof(f77,plain,(
% 3.71/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f56])).
% 3.71/0.99  
% 3.71/0.99  fof(f9,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f28,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.71/0.99    inference(ennf_transformation,[],[f9])).
% 3.71/0.99  
% 3.71/0.99  fof(f29,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.71/0.99    inference(flattening,[],[f28])).
% 3.71/0.99  
% 3.71/0.99  fof(f78,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f29])).
% 3.71/0.99  
% 3.71/0.99  fof(f98,plain,(
% 3.71/0.99    ~v1_xboole_0(sK3)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f99,plain,(
% 3.71/0.99    v1_funct_1(sK4)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f101,plain,(
% 3.71/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f16,axiom,(
% 3.71/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f38,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/0.99    inference(ennf_transformation,[],[f16])).
% 3.71/0.99  
% 3.71/0.99  fof(f39,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/0.99    inference(flattening,[],[f38])).
% 3.71/0.99  
% 3.71/0.99  fof(f88,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f39])).
% 3.71/0.99  
% 3.71/0.99  fof(f18,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f42,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f18])).
% 3.71/0.99  
% 3.71/0.99  fof(f43,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(flattening,[],[f42])).
% 3.71/0.99  
% 3.71/0.99  fof(f58,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(nnf_transformation,[],[f43])).
% 3.71/0.99  
% 3.71/0.99  fof(f95,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f112,plain,(
% 3.71/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(equality_resolution,[],[f95])).
% 3.71/0.99  
% 3.71/0.99  fof(f113,plain,(
% 3.71/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.71/0.99    inference(equality_resolution,[],[f112])).
% 3.71/0.99  
% 3.71/0.99  fof(f5,axiom,(
% 3.71/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f73,plain,(
% 3.71/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f5])).
% 3.71/0.99  
% 3.71/0.99  fof(f100,plain,(
% 3.71/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f67,plain,(
% 3.71/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f51])).
% 3.71/0.99  
% 3.71/0.99  fof(f76,plain,(
% 3.71/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f56])).
% 3.71/0.99  
% 3.71/0.99  fof(f94,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f114,plain,(
% 3.71/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.71/0.99    inference(equality_resolution,[],[f94])).
% 3.71/0.99  
% 3.71/0.99  fof(f15,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f36,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f15])).
% 3.71/0.99  
% 3.71/0.99  fof(f37,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(flattening,[],[f36])).
% 3.71/0.99  
% 3.71/0.99  fof(f86,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f37])).
% 3.71/0.99  
% 3.71/0.99  fof(f102,plain,(
% 3.71/0.99    v1_funct_1(sK5)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f90,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f14,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f35,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f14])).
% 3.71/0.99  
% 3.71/0.99  fof(f84,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f35])).
% 3.71/0.99  
% 3.71/0.99  fof(f11,axiom,(
% 3.71/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f31,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.71/0.99    inference(ennf_transformation,[],[f11])).
% 3.71/0.99  
% 3.71/0.99  fof(f32,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.71/0.99    inference(flattening,[],[f31])).
% 3.71/0.99  
% 3.71/0.99  fof(f81,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f32])).
% 3.71/0.99  
% 3.71/0.99  fof(f12,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f33,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f12])).
% 3.71/0.99  
% 3.71/0.99  fof(f82,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f33])).
% 3.71/0.99  
% 3.71/0.99  fof(f103,plain,(
% 3.71/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f105,plain,(
% 3.71/0.99    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f17,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f40,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.71/0.99    inference(ennf_transformation,[],[f17])).
% 3.71/0.99  
% 3.71/0.99  fof(f41,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.71/0.99    inference(flattening,[],[f40])).
% 3.71/0.99  
% 3.71/0.99  fof(f89,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f41])).
% 3.71/0.99  
% 3.71/0.99  fof(f19,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f44,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.71/0.99    inference(ennf_transformation,[],[f19])).
% 3.71/0.99  
% 3.71/0.99  fof(f45,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.71/0.99    inference(flattening,[],[f44])).
% 3.71/0.99  
% 3.71/0.99  fof(f96,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f45])).
% 3.71/0.99  
% 3.71/0.99  fof(f107,plain,(
% 3.71/0.99    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f20,axiom,(
% 3.71/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f46,plain,(
% 3.71/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.71/0.99    inference(ennf_transformation,[],[f20])).
% 3.71/0.99  
% 3.71/0.99  fof(f47,plain,(
% 3.71/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.71/0.99    inference(flattening,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  fof(f97,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f47])).
% 3.71/0.99  
% 3.71/0.99  fof(f13,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f23,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.71/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.71/0.99  
% 3.71/0.99  fof(f34,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f23])).
% 3.71/0.99  
% 3.71/0.99  fof(f83,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f34])).
% 3.71/0.99  
% 3.71/0.99  fof(f10,axiom,(
% 3.71/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f30,plain,(
% 3.71/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.71/0.99    inference(ennf_transformation,[],[f10])).
% 3.71/0.99  
% 3.71/0.99  fof(f57,plain,(
% 3.71/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.71/0.99    inference(nnf_transformation,[],[f30])).
% 3.71/0.99  
% 3.71/0.99  fof(f79,plain,(
% 3.71/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f57])).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f109]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3069,plain,
% 3.71/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_37,negated_conjecture,
% 3.71/0.99      ( m1_subset_1(sK6,sK2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3043,plain,
% 3.71/0.99      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3062,plain,
% 3.71/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.71/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.71/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5088,plain,
% 3.71/0.99      ( r2_hidden(sK6,sK2) = iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3043,c_3062]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_50,plain,
% 3.71/0.99      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_35,negated_conjecture,
% 3.71/0.99      ( k1_xboole_0 != sK2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_0,plain,
% 3.71/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.71/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3124,plain,
% 3.71/0.99      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3125,plain,
% 3.71/0.99      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3124]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3212,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK2) | v1_xboole_0(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3428,plain,
% 3.71/0.99      ( ~ m1_subset_1(sK6,sK2) | r2_hidden(sK6,sK2) | v1_xboole_0(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3212]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3429,plain,
% 3.71/0.99      ( m1_subset_1(sK6,sK2) != iProver_top
% 3.71/0.99      | r2_hidden(sK6,sK2) = iProver_top
% 3.71/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3428]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5444,plain,
% 3.71/0.99      ( r2_hidden(sK6,sK2) = iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_5088,c_50,c_35,c_3125,c_3429]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3061,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.71/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_14,plain,
% 3.71/0.99      ( m1_subset_1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.71/0.99      | ~ r2_hidden(X0,X2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3059,plain,
% 3.71/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.71/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6060,plain,
% 3.71/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.71/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.71/0.99      | r1_tarski(X2,X1) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3061,c_3059]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12978,plain,
% 3.71/0.99      ( m1_subset_1(sK6,X0) = iProver_top | r1_tarski(sK2,X0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_5444,c_6060]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_43,negated_conjecture,
% 3.71/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.71/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_44,plain,
% 3.71/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_42,negated_conjecture,
% 3.71/0.99      ( v1_funct_1(sK4) ),
% 3.71/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_45,plain,
% 3.71/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_40,negated_conjecture,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.71/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_47,plain,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_23,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | v1_xboole_0(X2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_26,plain,
% 3.71/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.71/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.71/0.99      | k1_xboole_0 = X0 ),
% 3.71/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_922,plain,
% 3.71/0.99      ( v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | v1_xboole_0(X2)
% 3.71/0.99      | X3 != X1
% 3.71/0.99      | k1_xboole_0 != X2
% 3.71/0.99      | k1_xboole_0 != X0
% 3.71/0.99      | k1_xboole_0 = X3 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_923,plain,
% 3.71/0.99      ( v1_partfun1(k1_xboole_0,X0)
% 3.71/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.71/0.99      | ~ v1_funct_1(k1_xboole_0)
% 3.71/0.99      | v1_xboole_0(k1_xboole_0)
% 3.71/0.99      | k1_xboole_0 = X0 ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_922]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9,plain,
% 3.71/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_937,plain,
% 3.71/0.99      ( v1_partfun1(k1_xboole_0,X0)
% 3.71/0.99      | ~ v1_funct_1(k1_xboole_0)
% 3.71/0.99      | v1_xboole_0(k1_xboole_0)
% 3.71/0.99      | k1_xboole_0 = X0 ),
% 3.71/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_923,c_9]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_942,plain,
% 3.71/0.99      ( k1_xboole_0 = X0
% 3.71/0.99      | v1_partfun1(k1_xboole_0,X0) = iProver_top
% 3.71/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.71/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_41,negated_conjecture,
% 3.71/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.71/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1095,plain,
% 3.71/0.99      ( v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | v1_xboole_0(X2)
% 3.71/0.99      | sK3 != X2
% 3.71/0.99      | sK2 != X1
% 3.71/0.99      | sK4 != X0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_41]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1096,plain,
% 3.71/0.99      ( v1_partfun1(sK4,sK2)
% 3.71/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.71/0.99      | ~ v1_funct_1(sK4)
% 3.71/0.99      | v1_xboole_0(sK3) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_1095]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1097,plain,
% 3.71/0.99      ( v1_partfun1(sK4,sK2) = iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top
% 3.71/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1,plain,
% 3.71/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.71/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3129,plain,
% 3.71/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.71/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.71/0.99      | k1_xboole_0 = sK2 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3130,plain,
% 3.71/0.99      ( k1_xboole_0 = sK2
% 3.71/0.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.71/0.99      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3129]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2207,plain,
% 3.71/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.71/0.99      theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3157,plain,
% 3.71/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2207]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3163,plain,
% 3.71/0.99      ( sK3 != X0
% 3.71/0.99      | v1_xboole_0(X0) != iProver_top
% 3.71/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3157]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3165,plain,
% 3.71/0.99      ( sK3 != k1_xboole_0
% 3.71/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.71/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3163]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_13,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3455,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3456,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.71/0.99      | r1_tarski(X0,sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3455]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3458,plain,
% 3.71/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
% 3.71/0.99      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3456]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3246,plain,
% 3.71/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3464,plain,
% 3.71/0.99      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3246]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2208,plain,
% 3.71/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.71/0.99      theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3232,plain,
% 3.71/0.99      ( ~ r1_tarski(X0,X1)
% 3.71/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.71/0.99      | sK2 != X0
% 3.71/0.99      | k1_xboole_0 != X1 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2208]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3490,plain,
% 3.71/0.99      ( ~ r1_tarski(sK2,X0)
% 3.71/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.71/0.99      | sK2 != sK2
% 3.71/0.99      | k1_xboole_0 != X0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3232]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3491,plain,
% 3.71/0.99      ( sK2 != sK2
% 3.71/0.99      | k1_xboole_0 != X0
% 3.71/0.99      | r1_tarski(sK2,X0) != iProver_top
% 3.71/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3490]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2213,plain,
% 3.71/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.71/0.99      theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3621,plain,
% 3.71/0.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK4) | X0 != sK4 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2213]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3622,plain,
% 3.71/0.99      ( X0 != sK4
% 3.71/0.99      | v1_funct_1(X0) = iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3621]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3624,plain,
% 3.71/0.99      ( k1_xboole_0 != sK4
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top
% 3.71/0.99      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3622]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3810,plain,
% 3.71/0.99      ( r1_tarski(sK2,sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_27,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/0.99      | k1_xboole_0 = X1
% 3.71/0.99      | k1_xboole_0 = X0 ),
% 3.71/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3132,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,sK2,k1_xboole_0)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.71/0.99      | k1_xboole_0 = X0
% 3.71/0.99      | k1_xboole_0 = sK2 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4341,plain,
% 3.71/0.99      ( ~ v1_funct_2(sK4,sK2,k1_xboole_0)
% 3.71/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.71/0.99      | k1_xboole_0 = sK2
% 3.71/0.99      | k1_xboole_0 = sK4 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_3132]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4344,plain,
% 3.71/0.99      ( k1_xboole_0 = sK2
% 3.71/0.99      | k1_xboole_0 = sK4
% 3.71/0.99      | v1_funct_2(sK4,sK2,k1_xboole_0) != iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_4341]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4513,plain,
% 3.71/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4514,plain,
% 3.71/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_4513]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_21,plain,
% 3.71/0.99      ( v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4468,plain,
% 3.71/0.99      ( v1_funct_2(sK4,X0,X1)
% 3.71/0.99      | ~ v1_partfun1(sK4,X0)
% 3.71/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.99      | ~ v1_funct_1(sK4) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6664,plain,
% 3.71/0.99      ( v1_funct_2(sK4,sK2,X0)
% 3.71/0.99      | ~ v1_partfun1(sK4,sK2)
% 3.71/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.71/0.99      | ~ v1_funct_1(sK4) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_4468]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6665,plain,
% 3.71/0.99      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.71/0.99      | v1_partfun1(sK4,sK2) != iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_6664]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6667,plain,
% 3.71/0.99      ( v1_funct_2(sK4,sK2,k1_xboole_0) = iProver_top
% 3.71/0.99      | v1_partfun1(sK4,sK2) != iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_6665]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9578,plain,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 3.71/0.99      | ~ r1_tarski(sK4,k2_zfmisc_1(sK2,X0)) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9579,plain,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.71/0.99      | r1_tarski(sK4,k2_zfmisc_1(sK2,X0)) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_9578]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9581,plain,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
% 3.71/0.99      | r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_9579]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_39,negated_conjecture,
% 3.71/0.99      ( v1_funct_1(sK5) ),
% 3.71/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3041,plain,
% 3.71/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3040,plain,
% 3.71/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_31,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.99      | k1_xboole_0 = X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3047,plain,
% 3.71/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.71/0.99      | k1_xboole_0 = X1
% 3.71/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6839,plain,
% 3.71/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3040,c_3047]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_20,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3056,plain,
% 3.71/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5006,plain,
% 3.71/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3040,c_3056]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6840,plain,
% 3.71/0.99      ( k1_relat_1(sK4) = sK2
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_6839,c_5006]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_46,plain,
% 3.71/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8527,plain,
% 3.71/0.99      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6840,c_46]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8528,plain,
% 3.71/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_8527]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_17,plain,
% 3.71/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.71/0.99      | ~ v1_funct_1(X2)
% 3.71/0.99      | ~ v1_funct_1(X1)
% 3.71/0.99      | ~ v1_relat_1(X1)
% 3.71/0.99      | ~ v1_relat_1(X2)
% 3.71/0.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3058,plain,
% 3.71/0.99      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.71/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_funct_1(X1) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8529,plain,
% 3.71/0.99      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_8528,c_3058]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_18,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3057,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4493,plain,
% 3.71/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3040,c_3057]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11711,plain,
% 3.71/0.99      ( v1_relat_1(X0) != iProver_top
% 3.71/0.99      | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_8529,c_45,c_4493]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11712,plain,
% 3.71/0.99      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | r2_hidden(X1,sK2) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_11711]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11718,plain,
% 3.71/0.99      ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_5444,c_11712]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11738,plain,
% 3.71/0.99      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3041,c_11718]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_38,negated_conjecture,
% 3.71/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.71/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3042,plain,
% 3.71/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4492,plain,
% 3.71/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3042,c_3057]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5005,plain,
% 3.71/0.99      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3042,c_3056]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_36,negated_conjecture,
% 3.71/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3044,plain,
% 3.71/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5240,plain,
% 3.71/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_5005,c_3044]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_25,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X3)
% 3.71/0.99      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 3.71/0.99      | k1_xboole_0 = X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3053,plain,
% 3.71/0.99      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 3.71/0.99      | k1_xboole_0 = X1
% 3.71/0.99      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.71/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.99      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.71/0.99      | v1_funct_1(X3) != iProver_top
% 3.71/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8002,plain,
% 3.71/0.99      ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.71/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.71/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.71/0.99      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.71/0.99      | v1_funct_1(X1) != iProver_top
% 3.71/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_5005,c_3053]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_48,plain,
% 3.71/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_49,plain,
% 3.71/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9736,plain,
% 3.71/0.99      ( v1_funct_1(X1) != iProver_top
% 3.71/0.99      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.71/0.99      | k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.71/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_8002,c_48,c_49]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9737,plain,
% 3.71/0.99      ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.71/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.71/0.99      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.71/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_9736]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9742,plain,
% 3.71/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_5240,c_9737]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_32,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.71/0.99      | ~ v1_funct_1(X3)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3046,plain,
% 3.71/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.71/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.71/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | v1_funct_1(X5) != iProver_top
% 3.71/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5717,plain,
% 3.71/0.99      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | v1_funct_1(X2) != iProver_top
% 3.71/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3042,c_3046]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6535,plain,
% 3.71/0.99      ( v1_funct_1(X2) != iProver_top
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5717,c_48]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6536,plain,
% 3.71/0.99      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_6535]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6544,plain,
% 3.71/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3040,c_6536]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_6643,plain,
% 3.71/0.99      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6544,c_45]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9743,plain,
% 3.71/0.99      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0
% 3.71/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.71/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.71/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_9742,c_6643]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9891,plain,
% 3.71/0.99      ( sK3 = k1_xboole_0
% 3.71/0.99      | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_9743,c_45,c_46,c_47]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9892,plain,
% 3.71/0.99      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.71/0.99      | sK3 = k1_xboole_0 ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_9891]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_34,negated_conjecture,
% 3.71/0.99      ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 3.71/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_9893,plain,
% 3.71/0.99      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 3.71/0.99      | sK3 = k1_xboole_0 ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_9892,c_34]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11915,plain,
% 3.71/0.99      ( sK3 = k1_xboole_0 ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_11738,c_4492,c_9893]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3060,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4066,plain,
% 3.71/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3040,c_3060]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11963,plain,
% 3.71/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_11915,c_4066]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3063,plain,
% 3.71/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3055,plain,
% 3.71/0.99      ( v1_funct_2(X0,X1,X2) = iProver_top
% 3.71/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.71/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_7178,plain,
% 3.71/0.99      ( v1_funct_2(k1_xboole_0,X0,X1) = iProver_top
% 3.71/0.99      | v1_partfun1(k1_xboole_0,X0) != iProver_top
% 3.71/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3063,c_3055]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_13450,plain,
% 3.71/0.99      ( v1_partfun1(k1_xboole_0,X0) != iProver_top
% 3.71/0.99      | v1_funct_2(k1_xboole_0,X0,X1) = iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_7178,c_44,c_45,c_47,c_35,c_1097,c_3624,c_4344,c_6667,
% 3.71/0.99                 c_9581,c_11963]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_13451,plain,
% 3.71/0.99      ( v1_funct_2(k1_xboole_0,X0,X1) = iProver_top
% 3.71/0.99      | v1_partfun1(k1_xboole_0,X0) != iProver_top ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_13450]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_33,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.71/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3045,plain,
% 3.71/0.99      ( k1_relset_1(X0,X0,X1) = X0
% 3.71/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.71/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.71/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4996,plain,
% 3.71/0.99      ( k1_relset_1(X0,X0,k1_xboole_0) = X0
% 3.71/0.99      | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top
% 3.71/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3063,c_3045]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12606,plain,
% 3.71/0.99      ( v1_funct_2(k1_xboole_0,X0,X0) != iProver_top
% 3.71/0.99      | k1_relset_1(X0,X0,k1_xboole_0) = X0 ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_4996,c_44,c_45,c_47,c_35,c_1097,c_3624,c_4344,c_6667,
% 3.71/0.99                 c_9581,c_11963]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12607,plain,
% 3.71/0.99      ( k1_relset_1(X0,X0,k1_xboole_0) = X0
% 3.71/0.99      | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_12606]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5003,plain,
% 3.71/0.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3063,c_3056]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_19,plain,
% 3.71/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_16,plain,
% 3.71/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_540,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.99      | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_544,plain,
% 3.71/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_540,c_18]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_545,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.71/0.99      inference(renaming,[status(thm)],[c_544]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3035,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3685,plain,
% 3.71/0.99      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3063,c_3035]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4064,plain,
% 3.71/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3063,c_3060]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3070,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.71/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5100,plain,
% 3.71/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_4064,c_3070]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8186,plain,
% 3.71/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3685,c_5100]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12612,plain,
% 3.71/0.99      ( k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,X0) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_12607,c_5003,c_8186]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_13456,plain,
% 3.71/0.99      ( k1_xboole_0 = X0 | v1_partfun1(k1_xboole_0,X0) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_13451,c_12612]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_14483,plain,
% 3.71/0.99      ( r1_tarski(sK2,X0) != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_12978,c_44,c_45,c_47,c_35,c_942,c_1097,c_3130,c_3165,
% 3.71/0.99                 c_3458,c_3464,c_3491,c_3624,c_3810,c_4344,c_4492,c_4514,
% 3.71/0.99                 c_6667,c_9581,c_9893,c_11738,c_11963,c_13456]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_14489,plain,
% 3.71/0.99      ( $false ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3069,c_14483]) ).
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  ------                               Statistics
% 3.71/0.99  
% 3.71/0.99  ------ General
% 3.71/0.99  
% 3.71/0.99  abstr_ref_over_cycles:                  0
% 3.71/0.99  abstr_ref_under_cycles:                 0
% 3.71/0.99  gc_basic_clause_elim:                   0
% 3.71/0.99  forced_gc_time:                         0
% 3.71/0.99  parsing_time:                           0.012
% 3.71/0.99  unif_index_cands_time:                  0.
% 3.71/0.99  unif_index_add_time:                    0.
% 3.71/0.99  orderings_time:                         0.
% 3.71/0.99  out_proof_time:                         0.017
% 3.71/0.99  total_time:                             0.397
% 3.71/0.99  num_of_symbols:                         57
% 3.71/0.99  num_of_terms:                           15158
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing
% 3.71/0.99  
% 3.71/0.99  num_of_splits:                          0
% 3.71/0.99  num_of_split_atoms:                     0
% 3.71/0.99  num_of_reused_defs:                     0
% 3.71/0.99  num_eq_ax_congr_red:                    44
% 3.71/0.99  num_of_sem_filtered_clauses:            1
% 3.71/0.99  num_of_subtypes:                        0
% 3.71/0.99  monotx_restored_types:                  0
% 3.71/0.99  sat_num_of_epr_types:                   0
% 3.71/0.99  sat_num_of_non_cyclic_types:            0
% 3.71/0.99  sat_guarded_non_collapsed_types:        0
% 3.71/0.99  num_pure_diseq_elim:                    0
% 3.71/0.99  simp_replaced_by:                       0
% 3.71/0.99  res_preprocessed:                       187
% 3.71/0.99  prep_upred:                             0
% 3.71/0.99  prep_unflattend:                        168
% 3.71/0.99  smt_new_axioms:                         0
% 3.71/0.99  pred_elim_cands:                        8
% 3.71/0.99  pred_elim:                              1
% 3.71/0.99  pred_elim_cl:                           2
% 3.71/0.99  pred_elim_cycles:                       7
% 3.71/0.99  merged_defs:                            16
% 3.71/0.99  merged_defs_ncl:                        0
% 3.71/0.99  bin_hyper_res:                          17
% 3.71/0.99  prep_cycles:                            4
% 3.71/0.99  pred_elim_time:                         0.026
% 3.71/0.99  splitting_time:                         0.
% 3.71/0.99  sem_filter_time:                        0.
% 3.71/0.99  monotx_time:                            0.001
% 3.71/0.99  subtype_inf_time:                       0.
% 3.71/0.99  
% 3.71/0.99  ------ Problem properties
% 3.71/0.99  
% 3.71/0.99  clauses:                                39
% 3.71/0.99  conjectures:                            10
% 3.71/0.99  epr:                                    11
% 3.71/0.99  horn:                                   31
% 3.71/0.99  ground:                                 10
% 3.71/0.99  unary:                                  13
% 3.71/0.99  binary:                                 8
% 3.71/0.99  lits:                                   100
% 3.71/0.99  lits_eq:                                21
% 3.71/0.99  fd_pure:                                0
% 3.71/0.99  fd_pseudo:                              0
% 3.71/0.99  fd_cond:                                5
% 3.71/0.99  fd_pseudo_cond:                         3
% 3.71/0.99  ac_symbols:                             0
% 3.71/0.99  
% 3.71/0.99  ------ Propositional Solver
% 3.71/0.99  
% 3.71/0.99  prop_solver_calls:                      28
% 3.71/0.99  prop_fast_solver_calls:                 1737
% 3.71/0.99  smt_solver_calls:                       0
% 3.71/0.99  smt_fast_solver_calls:                  0
% 3.71/0.99  prop_num_of_clauses:                    5890
% 3.71/0.99  prop_preprocess_simplified:             14176
% 3.71/0.99  prop_fo_subsumed:                       57
% 3.71/0.99  prop_solver_time:                       0.
% 3.71/0.99  smt_solver_time:                        0.
% 3.71/0.99  smt_fast_solver_time:                   0.
% 3.71/0.99  prop_fast_solver_time:                  0.
% 3.71/0.99  prop_unsat_core_time:                   0.
% 3.71/0.99  
% 3.71/0.99  ------ QBF
% 3.71/0.99  
% 3.71/0.99  qbf_q_res:                              0
% 3.71/0.99  qbf_num_tautologies:                    0
% 3.71/0.99  qbf_prep_cycles:                        0
% 3.71/0.99  
% 3.71/0.99  ------ BMC1
% 3.71/0.99  
% 3.71/0.99  bmc1_current_bound:                     -1
% 3.71/0.99  bmc1_last_solved_bound:                 -1
% 3.71/0.99  bmc1_unsat_core_size:                   -1
% 3.71/0.99  bmc1_unsat_core_parents_size:           -1
% 3.71/0.99  bmc1_merge_next_fun:                    0
% 3.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation
% 3.71/0.99  
% 3.71/0.99  inst_num_of_clauses:                    1576
% 3.71/0.99  inst_num_in_passive:                    288
% 3.71/0.99  inst_num_in_active:                     650
% 3.71/0.99  inst_num_in_unprocessed:                640
% 3.71/0.99  inst_num_of_loops:                      740
% 3.71/0.99  inst_num_of_learning_restarts:          0
% 3.71/0.99  inst_num_moves_active_passive:          89
% 3.71/0.99  inst_lit_activity:                      0
% 3.71/0.99  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      946
% 3.71/1.00  inst_num_of_non_proper_insts:           1950
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       191
% 3.71/1.00  res_forward_subset_subsumed:            171
% 3.71/1.00  res_backward_subset_subsumed:           6
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     2
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       716
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      107
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     198
% 3.71/1.00  sup_num_in_active:                      77
% 3.71/1.00  sup_num_in_passive:                     121
% 3.71/1.00  sup_num_of_loops:                       147
% 3.71/1.00  sup_fw_superposition:                   144
% 3.71/1.00  sup_bw_superposition:                   133
% 3.71/1.00  sup_immediate_simplified:               52
% 3.71/1.00  sup_given_eliminated:                   2
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    25
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 19
% 3.71/1.00  sim_bw_subset_subsumed:                 13
% 3.71/1.00  sim_fw_subsumed:                        11
% 3.71/1.00  sim_bw_subsumed:                        5
% 3.71/1.00  sim_fw_subsumption_res:                 0
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      5
% 3.71/1.00  sim_eq_tautology_del:                   13
% 3.71/1.00  sim_eq_res_simp:                        2
% 3.71/1.00  sim_fw_demodulated:                     10
% 3.71/1.00  sim_bw_demodulated:                     66
% 3.71/1.00  sim_light_normalised:                   22
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
