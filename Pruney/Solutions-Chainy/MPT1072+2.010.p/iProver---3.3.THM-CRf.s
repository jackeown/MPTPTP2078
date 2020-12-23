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
% DateTime   : Thu Dec  3 12:09:59 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  170 (4665 expanded)
%              Number of clauses        :  105 (1133 expanded)
%              Number of leaves         :   21 (1590 expanded)
%              Depth                    :   28
%              Number of atoms          :  473 (28097 expanded)
%              Number of equality atoms :  179 (2400 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(k3_funct_2(X0,X1,sK5,X2),k2_relset_1(X0,X1,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r2_hidden(k3_funct_2(X0,X1,X3,sK4),k2_relset_1(X0,X1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k3_funct_2(X0,sK3,X3,X2),k2_relset_1(X0,sK3,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
                & v1_funct_2(X3,X0,sK3)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,X0) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(sK2,X1,X3,X2),k2_relset_1(sK2,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
                  & v1_funct_2(X3,sK2,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,sK2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,sK2)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f41,f40,f39,f38])).

fof(f64,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ~ r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1182,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_284,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_288,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_20,c_18])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_1165,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1246,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | r2_hidden(sK4,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_1313,plain,
    ( m1_subset_1(sK4,sK2) != iProver_top
    | r2_hidden(sK4,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_1379,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5))
    | ~ r2_hidden(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_1380,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5)) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_1168,plain,
    ( m1_subset_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK5 != X2
    | sK3 != X3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK2)
    | k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_23,c_20,c_18])).

cnf(c_1164,plain,
    ( k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1448,plain,
    ( k3_funct_2(sK2,sK3,sK5,sK4) = k1_funct_1(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1168,c_1164])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1170,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1529,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1448,c_1170])).

cnf(c_1725,plain,
    ( k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_24,c_26,c_1313,c_1380,c_1529])).

cnf(c_1169,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1730,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1725,c_1169])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1732,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1730,c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1171,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1868,plain,
    ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1171])).

cnf(c_2585,plain,
    ( k2_relset_1(k1_xboole_0,X0,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1732,c_1868])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1172,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2778,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_1172])).

cnf(c_2779,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2778,c_6])).

cnf(c_2985,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2779,c_1732])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2990,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_1175])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1174,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3343,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2990,c_1174])).

cnf(c_3828,plain,
    ( v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_3343])).

cnf(c_2584,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1868])).

cnf(c_2586,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2584,c_5])).

cnf(c_3129,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,k2_relat_1(sK5))) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,k2_relat_1(sK5))) ),
    inference(superposition,[status(thm)],[c_2985,c_2586])).

cnf(c_1867,plain,
    ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1171])).

cnf(c_2431,plain,
    ( k2_relset_1(X0,k1_xboole_0,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1732,c_1867])).

cnf(c_2566,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_1172])).

cnf(c_2571,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2566,c_5])).

cnf(c_2628,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_1732])).

cnf(c_2634,plain,
    ( k2_relset_1(X0,k1_xboole_0,k2_relat_1(sK5)) = k2_relat_1(k2_relat_1(sK5)) ),
    inference(superposition,[status(thm)],[c_2628,c_1867])).

cnf(c_3130,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(k2_relat_1(sK5))) = k2_relat_1(k2_relat_1(k2_relat_1(sK5))) ),
    inference(demodulation,[status(thm)],[c_3129,c_2634])).

cnf(c_3986,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_1172])).

cnf(c_3987,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3986,c_6])).

cnf(c_2633,plain,
    ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(sK5)) = k2_relat_1(k2_relat_1(sK5)) ),
    inference(superposition,[status(thm)],[c_2628,c_1868])).

cnf(c_3345,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_1172])).

cnf(c_3346,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3345,c_6])).

cnf(c_3348,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3346])).

cnf(c_4109,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_1732,c_2571,c_3348])).

cnf(c_2567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1175])).

cnf(c_4625,plain,
    ( r1_tarski(k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k2_relat_1(sK5)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_2567])).

cnf(c_4116,plain,
    ( k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k2_relat_1(sK5)))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5)))) ),
    inference(superposition,[status(thm)],[c_4109,c_1171])).

cnf(c_4628,plain,
    ( r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5)))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4625,c_4116])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4621,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_2567])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3048,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1173])).

cnf(c_3055,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_3048])).

cnf(c_15577,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_3055])).

cnf(c_15592,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_relset_1(X2,k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15577,c_5])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_719,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1227,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1233,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_1235,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_718,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1302,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1443,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_1444,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_717,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1620,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1179,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1180,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2290,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1180])).

cnf(c_9417,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_3055])).

cnf(c_15871,plain,
    ( v1_xboole_0(X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15592,c_24,c_25,c_26,c_1235,c_1313,c_1380,c_1444,c_1529,c_1620,c_3055,c_9417])).

cnf(c_15872,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15871])).

cnf(c_15884,plain,
    ( v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_15872])).

cnf(c_16129,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3828,c_15884])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     num_symb
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       true
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 22
% 3.85/0.98  conjectures                             5
% 3.85/0.98  EPR                                     7
% 3.85/0.98  Horn                                    17
% 3.85/0.98  unary                                   7
% 3.85/0.98  binary                                  10
% 3.85/0.98  lits                                    42
% 3.85/0.98  lits eq                                 8
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 1
% 3.85/0.98  fd_pseudo_cond                          0
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Schedule dynamic 5 is on 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     none
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       false
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98   Resolution empty clause
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.85/0.98    inference(nnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.85/0.98    inference(rectify,[],[f27])).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f30])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.85/0.98    inference(ennf_transformation,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.85/0.98    inference(flattening,[],[f23])).
% 3.85/0.98  
% 3.85/0.98  fof(f59,plain,(
% 3.85/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,conjecture,(
% 3.85/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f13,negated_conjecture,(
% 3.85/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 3.85/0.98    inference(negated_conjecture,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.85/0.98    inference(flattening,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k3_funct_2(X0,X1,sK5,X2),k2_relset_1(X0,X1,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) => (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,sK4),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(sK4,X0))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,sK3,X3,X2),k2_relset_1(X0,sK3,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) & v1_funct_2(X3,X0,sK3) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(sK3))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK2,X1,X3,X2),k2_relset_1(sK2,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X3,sK2,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    (((~r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,sK2)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f41,f40,f39,f38])).
% 3.85/0.98  
% 3.85/0.98  fof(f64,plain,(
% 3.85/0.98    v1_funct_2(sK5,sK2,sK3)),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f63,plain,(
% 3.85/0.98    v1_funct_1(sK5)),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f65,plain,(
% 3.85/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f60,plain,(
% 3.85/0.98    ~v1_xboole_0(sK2)),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f62,plain,(
% 3.85/0.98    m1_subset_1(sK4,sK2)),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f15,plain,(
% 3.85/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f16,plain,(
% 3.85/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f51,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.85/0.98    inference(flattening,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f58,plain,(
% 3.85/0.98    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f22])).
% 3.85/0.98  
% 3.85/0.98  fof(f66,plain,(
% 3.85/0.98    ~r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5))),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.85/0.98    inference(nnf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.85/0.98    inference(flattening,[],[f35])).
% 3.85/0.98  
% 3.85/0.98  fof(f50,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.85/0.98    inference(cnf_transformation,[],[f36])).
% 3.85/0.98  
% 3.85/0.98  fof(f67,plain,(
% 3.85/0.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.85/0.98    inference(equality_resolution,[],[f50])).
% 3.85/0.98  
% 3.85/0.98  fof(f49,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f36])).
% 3.85/0.98  
% 3.85/0.98  fof(f68,plain,(
% 3.85/0.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.85/0.98    inference(equality_resolution,[],[f49])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.85/0.98    inference(ennf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f57,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f20])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.85/0.98    inference(ennf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f56,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f37,plain,(
% 3.85/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.85/0.98    inference(nnf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f52,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f37])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f17,plain,(
% 3.85/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f54,plain,(
% 3.85/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f53,plain,(
% 3.85/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f37])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f55,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f61,plain,(
% 3.85/0.98    ~v1_xboole_0(sK3)),
% 3.85/0.98    inference(cnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f14,plain,(
% 3.85/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(nnf_transformation,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(rectify,[],[f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f34])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f34])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1182,plain,
% 3.85/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_16,plain,
% 3.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | ~ r2_hidden(X3,X1)
% 3.85/0.98      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.85/0.98      | ~ v1_funct_1(X0)
% 3.85/0.98      | k1_xboole_0 = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_19,negated_conjecture,
% 3.85/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.85/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_283,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | ~ r2_hidden(X3,X1)
% 3.85/0.98      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.85/0.98      | ~ v1_funct_1(X0)
% 3.85/0.98      | sK5 != X0
% 3.85/0.98      | sK3 != X2
% 3.85/0.98      | sK2 != X1
% 3.85/0.98      | k1_xboole_0 = X2 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_284,plain,
% 3.85/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.85/0.98      | ~ r2_hidden(X0,sK2)
% 3.85/0.98      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
% 3.85/0.98      | ~ v1_funct_1(sK5)
% 3.85/0.98      | k1_xboole_0 = sK3 ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_283]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_20,negated_conjecture,
% 3.85/0.98      ( v1_funct_1(sK5) ),
% 3.85/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_18,negated_conjecture,
% 3.85/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_288,plain,
% 3.85/0.98      ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
% 3.85/0.98      | ~ r2_hidden(X0,sK2)
% 3.85/0.98      | k1_xboole_0 = sK3 ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_284,c_20,c_18]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_289,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,sK2)
% 3.85/0.98      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5))
% 3.85/0.98      | k1_xboole_0 = sK3 ),
% 3.85/0.98      inference(renaming,[status(thm)],[c_288]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1165,plain,
% 3.85/0.98      ( k1_xboole_0 = sK3
% 3.85/0.98      | r2_hidden(X0,sK2) != iProver_top
% 3.85/0.98      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK2,sK3,sK5)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_23,negated_conjecture,
% 3.85/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_24,plain,
% 3.85/0.98      ( v1_xboole_0(sK2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_21,negated_conjecture,
% 3.85/0.98      ( m1_subset_1(sK4,sK2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_26,plain,
% 3.85/0.98      ( m1_subset_1(sK4,sK2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1246,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK2) | v1_xboole_0(sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1312,plain,
% 3.85/0.98      ( ~ m1_subset_1(sK4,sK2) | r2_hidden(sK4,sK2) | v1_xboole_0(sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1246]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1313,plain,
% 3.85/0.98      ( m1_subset_1(sK4,sK2) != iProver_top
% 3.85/0.98      | r2_hidden(sK4,sK2) = iProver_top
% 3.85/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1379,plain,
% 3.85/0.98      ( r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5))
% 3.85/0.98      | ~ r2_hidden(sK4,sK2)
% 3.85/0.98      | k1_xboole_0 = sK3 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_289]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1380,plain,
% 3.85/0.98      ( k1_xboole_0 = sK3
% 3.85/0.98      | r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5)) = iProver_top
% 3.85/0.98      | r2_hidden(sK4,sK2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1379]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1168,plain,
% 3.85/0.98      ( m1_subset_1(sK4,sK2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15,plain,
% 3.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.85/0.98      | ~ m1_subset_1(X3,X1)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | ~ v1_funct_1(X0)
% 3.85/0.98      | v1_xboole_0(X1)
% 3.85/0.98      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.85/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_304,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.85/0.98      | ~ v1_funct_1(X2)
% 3.85/0.98      | v1_xboole_0(X1)
% 3.85/0.98      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 3.85/0.98      | sK5 != X2
% 3.85/0.98      | sK3 != X3
% 3.85/0.98      | sK2 != X1 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_305,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.85/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.85/0.98      | ~ v1_funct_1(sK5)
% 3.85/0.98      | v1_xboole_0(sK2)
% 3.85/0.98      | k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_304]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_309,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.85/0.98      | k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_305,c_23,c_20,c_18]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1164,plain,
% 3.85/0.98      ( k3_funct_2(sK2,sK3,sK5,X0) = k1_funct_1(sK5,X0)
% 3.85/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1448,plain,
% 3.85/0.98      ( k3_funct_2(sK2,sK3,sK5,sK4) = k1_funct_1(sK5,sK4) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1168,c_1164]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_17,negated_conjecture,
% 3.85/0.98      ( ~ r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1170,plain,
% 3.85/0.98      ( r2_hidden(k3_funct_2(sK2,sK3,sK5,sK4),k2_relset_1(sK2,sK3,sK5)) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1529,plain,
% 3.85/0.98      ( r2_hidden(k1_funct_1(sK5,sK4),k2_relset_1(sK2,sK3,sK5)) != iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1448,c_1170]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1725,plain,
% 3.85/0.98      ( k1_xboole_0 = sK3 ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_1165,c_24,c_26,c_1313,c_1380,c_1529]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1169,plain,
% 3.85/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1730,plain,
% 3.85/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1725,c_1169]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1732,plain,
% 3.85/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1730,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_14,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1171,plain,
% 3.85/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1868,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_6,c_1171]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2585,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,sK5) = k2_relat_1(sK5) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1732,c_1868]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_13,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1172,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.85/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2778,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2585,c_1172]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2779,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_2778,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2985,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2779,c_1732]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1175,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2990,plain,
% 3.85/0.98      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2985,c_1175]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1174,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3343,plain,
% 3.85/0.98      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2990,c_1174]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3828,plain,
% 3.85/0.98      ( v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1182,c_3343]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2584,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 3.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1172,c_1868]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2586,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,X2)) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,X2))
% 3.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2584,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3129,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,k2_relset_1(X1,k1_xboole_0,k2_relat_1(sK5))) = k2_relat_1(k2_relset_1(X1,k1_xboole_0,k2_relat_1(sK5))) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2985,c_2586]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1867,plain,
% 3.85/0.98      ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_5,c_1171]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2431,plain,
% 3.85/0.98      ( k2_relset_1(X0,k1_xboole_0,sK5) = k2_relat_1(sK5) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1732,c_1867]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2566,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.85/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2431,c_1172]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2571,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.85/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_2566,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2628,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2571,c_1732]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2634,plain,
% 3.85/0.98      ( k2_relset_1(X0,k1_xboole_0,k2_relat_1(sK5)) = k2_relat_1(k2_relat_1(sK5)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2628,c_1867]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3130,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(k2_relat_1(sK5))) = k2_relat_1(k2_relat_1(k2_relat_1(sK5))) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3129,c_2634]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3986,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3130,c_1172]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3987,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_3986,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2633,plain,
% 3.85/0.98      ( k2_relset_1(k1_xboole_0,X0,k2_relat_1(sK5)) = k2_relat_1(k2_relat_1(sK5)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2628,c_1868]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3345,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2633,c_1172]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3346,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(X0)) = iProver_top
% 3.85/0.98      | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_3345,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3348,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(sK5)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.85/0.98      | m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3346]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4109,plain,
% 3.85/0.98      ( m1_subset_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5))),k1_zfmisc_1(X0)) = iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_3987,c_1732,c_2571,c_3348]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2567,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.85/0.98      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1172,c_1175]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4625,plain,
% 3.85/0.98      ( r1_tarski(k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k2_relat_1(sK5)))),X1) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4109,c_2567]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4116,plain,
% 3.85/0.98      ( k2_relset_1(X0,X1,k2_relat_1(k2_relat_1(k2_relat_1(sK5)))) = k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5)))) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4109,c_1171]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4628,plain,
% 3.85/0.98      ( r1_tarski(k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(sK5)))),X0) = iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_4625,c_4116]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1176,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.85/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4621,plain,
% 3.85/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.85/0.98      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1176,c_2567]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_12,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/0.98      | ~ v1_xboole_0(X1)
% 3.85/0.98      | v1_xboole_0(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1173,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.85/0.98      | v1_xboole_0(X1) != iProver_top
% 3.85/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3048,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.85/0.98      | v1_xboole_0(X1) != iProver_top
% 3.85/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_5,c_1173]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3055,plain,
% 3.85/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.85/0.98      | v1_xboole_0(X1) != iProver_top
% 3.85/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1176,c_3048]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15577,plain,
% 3.85/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top
% 3.85/0.98      | v1_xboole_0(X2) != iProver_top
% 3.85/0.98      | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4621,c_3055]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15592,plain,
% 3.85/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.85/0.98      | v1_xboole_0(X1) != iProver_top
% 3.85/0.98      | v1_xboole_0(k2_relset_1(X2,k1_xboole_0,X0)) = iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_15577,c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_22,negated_conjecture,
% 3.85/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.85/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_25,plain,
% 3.85/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_719,plain,
% 3.85/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.85/0.98      theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1227,plain,
% 3.85/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_719]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1233,plain,
% 3.85/0.98      ( sK3 != X0
% 3.85/0.98      | v1_xboole_0(X0) != iProver_top
% 3.85/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1235,plain,
% 3.85/0.98      ( sK3 != k1_xboole_0
% 3.85/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.85/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1233]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_718,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1302,plain,
% 3.85/0.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_718]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1443,plain,
% 3.85/0.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1302]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1444,plain,
% 3.85/0.98      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1443]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_717,plain,( X0 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1620,plain,
% 3.85/0.98      ( sK3 = sK3 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_717]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1179,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.85/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1180,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.85/0.98      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2290,plain,
% 3.85/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1179,c_1180]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9417,plain,
% 3.85/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.85/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2290,c_3055]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15871,plain,
% 3.85/0.98      ( v1_xboole_0(X1) != iProver_top
% 3.85/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_15592,c_24,c_25,c_26,c_1235,c_1313,c_1380,c_1444,c_1529,
% 3.85/0.99                 c_1620,c_3055,c_9417]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15872,plain,
% 3.85/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.85/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_15871]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15884,plain,
% 3.85/0.99      ( v1_xboole_0(X0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_4628,c_15872]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_16129,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3828,c_15884]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ General
% 3.85/0.99  
% 3.85/0.99  abstr_ref_over_cycles:                  0
% 3.85/0.99  abstr_ref_under_cycles:                 0
% 3.85/0.99  gc_basic_clause_elim:                   0
% 3.85/0.99  forced_gc_time:                         0
% 3.85/0.99  parsing_time:                           0.009
% 3.85/0.99  unif_index_cands_time:                  0.
% 3.85/0.99  unif_index_add_time:                    0.
% 3.85/0.99  orderings_time:                         0.
% 3.85/0.99  out_proof_time:                         0.011
% 3.85/0.99  total_time:                             0.499
% 3.85/0.99  num_of_symbols:                         50
% 3.85/0.99  num_of_terms:                           15086
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing
% 3.85/0.99  
% 3.85/0.99  num_of_splits:                          0
% 3.85/0.99  num_of_split_atoms:                     0
% 3.85/0.99  num_of_reused_defs:                     0
% 3.85/0.99  num_eq_ax_congr_red:                    22
% 3.85/0.99  num_of_sem_filtered_clauses:            1
% 3.85/0.99  num_of_subtypes:                        0
% 3.85/0.99  monotx_restored_types:                  0
% 3.85/0.99  sat_num_of_epr_types:                   0
% 3.85/0.99  sat_num_of_non_cyclic_types:            0
% 3.85/0.99  sat_guarded_non_collapsed_types:        0
% 3.85/0.99  num_pure_diseq_elim:                    0
% 3.85/0.99  simp_replaced_by:                       0
% 3.85/0.99  res_preprocessed:                       111
% 3.85/0.99  prep_upred:                             0
% 3.85/0.99  prep_unflattend:                        6
% 3.85/0.99  smt_new_axioms:                         0
% 3.85/0.99  pred_elim_cands:                        4
% 3.85/0.99  pred_elim:                              2
% 3.85/0.99  pred_elim_cl:                           2
% 3.85/0.99  pred_elim_cycles:                       4
% 3.85/0.99  merged_defs:                            8
% 3.85/0.99  merged_defs_ncl:                        0
% 3.85/0.99  bin_hyper_res:                          8
% 3.85/0.99  prep_cycles:                            4
% 3.85/0.99  pred_elim_time:                         0.004
% 3.85/0.99  splitting_time:                         0.
% 3.85/0.99  sem_filter_time:                        0.
% 3.85/0.99  monotx_time:                            0.
% 3.85/0.99  subtype_inf_time:                       0.
% 3.85/0.99  
% 3.85/0.99  ------ Problem properties
% 3.85/0.99  
% 3.85/0.99  clauses:                                22
% 3.85/0.99  conjectures:                            5
% 3.85/0.99  epr:                                    7
% 3.85/0.99  horn:                                   17
% 3.85/0.99  ground:                                 5
% 3.85/0.99  unary:                                  7
% 3.85/0.99  binary:                                 10
% 3.85/0.99  lits:                                   42
% 3.85/0.99  lits_eq:                                8
% 3.85/0.99  fd_pure:                                0
% 3.85/0.99  fd_pseudo:                              0
% 3.85/0.99  fd_cond:                                1
% 3.85/0.99  fd_pseudo_cond:                         0
% 3.85/0.99  ac_symbols:                             0
% 3.85/0.99  
% 3.85/0.99  ------ Propositional Solver
% 3.85/0.99  
% 3.85/0.99  prop_solver_calls:                      33
% 3.85/0.99  prop_fast_solver_calls:                 1234
% 3.85/0.99  smt_solver_calls:                       0
% 3.85/0.99  smt_fast_solver_calls:                  0
% 3.85/0.99  prop_num_of_clauses:                    6208
% 3.85/0.99  prop_preprocess_simplified:             12728
% 3.85/0.99  prop_fo_subsumed:                       125
% 3.85/0.99  prop_solver_time:                       0.
% 3.85/0.99  smt_solver_time:                        0.
% 3.85/0.99  smt_fast_solver_time:                   0.
% 3.85/0.99  prop_fast_solver_time:                  0.
% 3.85/0.99  prop_unsat_core_time:                   0.
% 3.85/0.99  
% 3.85/0.99  ------ QBF
% 3.85/0.99  
% 3.85/0.99  qbf_q_res:                              0
% 3.85/0.99  qbf_num_tautologies:                    0
% 3.85/0.99  qbf_prep_cycles:                        0
% 3.85/0.99  
% 3.85/0.99  ------ BMC1
% 3.85/0.99  
% 3.85/0.99  bmc1_current_bound:                     -1
% 3.85/0.99  bmc1_last_solved_bound:                 -1
% 3.85/0.99  bmc1_unsat_core_size:                   -1
% 3.85/0.99  bmc1_unsat_core_parents_size:           -1
% 3.85/0.99  bmc1_merge_next_fun:                    0
% 3.85/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation
% 3.85/0.99  
% 3.85/0.99  inst_num_of_clauses:                    2027
% 3.85/0.99  inst_num_in_passive:                    288
% 3.85/0.99  inst_num_in_active:                     1101
% 3.85/0.99  inst_num_in_unprocessed:                638
% 3.85/0.99  inst_num_of_loops:                      1300
% 3.85/0.99  inst_num_of_learning_restarts:          0
% 3.85/0.99  inst_num_moves_active_passive:          195
% 3.85/0.99  inst_lit_activity:                      0
% 3.85/0.99  inst_lit_activity_moves:                0
% 3.85/0.99  inst_num_tautologies:                   0
% 3.85/0.99  inst_num_prop_implied:                  0
% 3.85/0.99  inst_num_existing_simplified:           0
% 3.85/0.99  inst_num_eq_res_simplified:             0
% 3.85/0.99  inst_num_child_elim:                    0
% 3.85/0.99  inst_num_of_dismatching_blockings:      994
% 3.85/0.99  inst_num_of_non_proper_insts:           2448
% 3.85/0.99  inst_num_of_duplicates:                 0
% 3.85/0.99  inst_inst_num_from_inst_to_res:         0
% 3.85/0.99  inst_dismatching_checking_time:         0.
% 3.85/0.99  
% 3.85/0.99  ------ Resolution
% 3.85/0.99  
% 3.85/0.99  res_num_of_clauses:                     0
% 3.85/0.99  res_num_in_passive:                     0
% 3.85/0.99  res_num_in_active:                      0
% 3.85/0.99  res_num_of_loops:                       115
% 3.85/0.99  res_forward_subset_subsumed:            128
% 3.85/0.99  res_backward_subset_subsumed:           0
% 3.85/0.99  res_forward_subsumed:                   0
% 3.85/0.99  res_backward_subsumed:                  0
% 3.85/0.99  res_forward_subsumption_resolution:     0
% 3.85/0.99  res_backward_subsumption_resolution:    0
% 3.85/0.99  res_clause_to_clause_subsumption:       1688
% 3.85/0.99  res_orphan_elimination:                 0
% 3.85/0.99  res_tautology_del:                      336
% 3.85/0.99  res_num_eq_res_simplified:              0
% 3.85/0.99  res_num_sel_changes:                    0
% 3.85/0.99  res_moves_from_active_to_pass:          0
% 3.85/0.99  
% 3.85/0.99  ------ Superposition
% 3.85/0.99  
% 3.85/0.99  sup_time_total:                         0.
% 3.85/0.99  sup_time_generating:                    0.
% 3.85/0.99  sup_time_sim_full:                      0.
% 3.85/0.99  sup_time_sim_immed:                     0.
% 3.85/0.99  
% 3.85/0.99  sup_num_of_clauses:                     348
% 3.85/0.99  sup_num_in_active:                      168
% 3.85/0.99  sup_num_in_passive:                     180
% 3.85/0.99  sup_num_of_loops:                       258
% 3.85/0.99  sup_fw_superposition:                   599
% 3.85/0.99  sup_bw_superposition:                   1004
% 3.85/0.99  sup_immediate_simplified:               679
% 3.85/0.99  sup_given_eliminated:                   1
% 3.85/0.99  comparisons_done:                       0
% 3.85/0.99  comparisons_avoided:                    0
% 3.85/0.99  
% 3.85/0.99  ------ Simplifications
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  sim_fw_subset_subsumed:                 88
% 3.85/0.99  sim_bw_subset_subsumed:                 17
% 3.85/0.99  sim_fw_subsumed:                        35
% 3.85/0.99  sim_bw_subsumed:                        82
% 3.85/0.99  sim_fw_subsumption_res:                 0
% 3.85/0.99  sim_bw_subsumption_res:                 0
% 3.85/0.99  sim_tautology_del:                      9
% 3.85/0.99  sim_eq_tautology_del:                   331
% 3.85/0.99  sim_eq_res_simp:                        0
% 3.85/0.99  sim_fw_demodulated:                     465
% 3.85/0.99  sim_bw_demodulated:                     15
% 3.85/0.99  sim_light_normalised:                   102
% 3.85/0.99  sim_joinable_taut:                      0
% 3.85/0.99  sim_joinable_simp:                      0
% 3.85/0.99  sim_ac_normalised:                      0
% 3.85/0.99  sim_smt_subsumption:                    0
% 3.85/0.99  
%------------------------------------------------------------------------------
