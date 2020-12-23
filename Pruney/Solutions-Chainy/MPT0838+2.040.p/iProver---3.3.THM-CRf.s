%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:33 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 288 expanded)
%              Number of clauses        :   74 ( 106 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   21
%              Number of atoms          :  406 (1064 expanded)
%              Number of equality atoms :  129 ( 250 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f47])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k1_relset_1(X0,X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK5))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK4,X2))
                | ~ m1_subset_1(X3,sK4) )
            & k1_xboole_0 != k1_relset_1(X0,sK4,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK3,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK3,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
        | ~ m1_subset_1(X3,sK4) )
    & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f54,f53,f52])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
      | ~ m1_subset_1(X3,sK4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
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

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2486,plain,
    ( m1_subset_1(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2484,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3582,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_2484])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2489,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2485,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2983,plain,
    ( m1_subset_1(sK1(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2489,c_2485])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2471,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2473,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3479,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2471,c_2473])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2488,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2472,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2975,plain,
    ( m1_subset_1(sK1(k2_relset_1(sK3,sK4,sK5),X0),sK4) != iProver_top
    | r1_xboole_0(k2_relset_1(sK3,sK4,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_2472])).

cnf(c_3658,plain,
    ( m1_subset_1(sK1(k2_relat_1(sK5),X0),sK4) != iProver_top
    | r1_xboole_0(k2_relat_1(sK5),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3479,c_2975])).

cnf(c_5337,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_3658])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2487,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5554,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
    | v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_2487])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_2468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2908,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_2468])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2480,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3956,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_2483])).

cnf(c_4128,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_3956])).

cnf(c_5612,plain,
    ( v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5554,c_2908,c_4128])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2491,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5616,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5612,c_2491])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2493,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2494,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3373,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_2494])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2482,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4604,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3373,c_2482])).

cnf(c_20,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2476,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4994,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4604,c_2476])).

cnf(c_5052,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_4128,c_4994])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2479,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4271,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_4128,c_2479])).

cnf(c_5057,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_5052,c_4271])).

cnf(c_19,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2477,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5129,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5057,c_2477])).

cnf(c_5132,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5129,c_4128])).

cnf(c_5133,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5132])).

cnf(c_5715,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5616,c_5133])).

cnf(c_5726,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5715])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2490,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7591,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5726,c_2490])).

cnf(c_8271,plain,
    ( v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3582,c_7591])).

cnf(c_9958,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8271,c_2491])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2474,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3532,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2471,c_2474])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3730,plain,
    ( k1_relat_1(sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3532,c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9958,c_3730])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.06/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.01  
% 3.06/1.01  ------  iProver source info
% 3.06/1.01  
% 3.06/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.01  git: non_committed_changes: false
% 3.06/1.01  git: last_make_outside_of_git: false
% 3.06/1.01  
% 3.06/1.01  ------ 
% 3.06/1.01  
% 3.06/1.01  ------ Input Options
% 3.06/1.01  
% 3.06/1.01  --out_options                           all
% 3.06/1.01  --tptp_safe_out                         true
% 3.06/1.01  --problem_path                          ""
% 3.06/1.01  --include_path                          ""
% 3.06/1.01  --clausifier                            res/vclausify_rel
% 3.06/1.01  --clausifier_options                    ""
% 3.06/1.01  --stdin                                 false
% 3.06/1.01  --stats_out                             all
% 3.06/1.01  
% 3.06/1.01  ------ General Options
% 3.06/1.01  
% 3.06/1.01  --fof                                   false
% 3.06/1.01  --time_out_real                         305.
% 3.06/1.01  --time_out_virtual                      -1.
% 3.06/1.01  --symbol_type_check                     false
% 3.06/1.01  --clausify_out                          false
% 3.06/1.01  --sig_cnt_out                           false
% 3.06/1.01  --trig_cnt_out                          false
% 3.06/1.01  --trig_cnt_out_tolerance                1.
% 3.06/1.01  --trig_cnt_out_sk_spl                   false
% 3.06/1.01  --abstr_cl_out                          false
% 3.06/1.01  
% 3.06/1.01  ------ Global Options
% 3.06/1.01  
% 3.06/1.01  --schedule                              default
% 3.06/1.01  --add_important_lit                     false
% 3.06/1.01  --prop_solver_per_cl                    1000
% 3.06/1.01  --min_unsat_core                        false
% 3.06/1.01  --soft_assumptions                      false
% 3.06/1.01  --soft_lemma_size                       3
% 3.06/1.01  --prop_impl_unit_size                   0
% 3.06/1.01  --prop_impl_unit                        []
% 3.06/1.01  --share_sel_clauses                     true
% 3.06/1.01  --reset_solvers                         false
% 3.06/1.01  --bc_imp_inh                            [conj_cone]
% 3.06/1.01  --conj_cone_tolerance                   3.
% 3.06/1.01  --extra_neg_conj                        none
% 3.06/1.01  --large_theory_mode                     true
% 3.06/1.01  --prolific_symb_bound                   200
% 3.06/1.01  --lt_threshold                          2000
% 3.06/1.01  --clause_weak_htbl                      true
% 3.06/1.01  --gc_record_bc_elim                     false
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing Options
% 3.06/1.01  
% 3.06/1.01  --preprocessing_flag                    true
% 3.06/1.01  --time_out_prep_mult                    0.1
% 3.06/1.01  --splitting_mode                        input
% 3.06/1.01  --splitting_grd                         true
% 3.06/1.01  --splitting_cvd                         false
% 3.06/1.01  --splitting_cvd_svl                     false
% 3.06/1.01  --splitting_nvd                         32
% 3.06/1.01  --sub_typing                            true
% 3.06/1.01  --prep_gs_sim                           true
% 3.06/1.01  --prep_unflatten                        true
% 3.06/1.01  --prep_res_sim                          true
% 3.06/1.01  --prep_upred                            true
% 3.06/1.01  --prep_sem_filter                       exhaustive
% 3.06/1.01  --prep_sem_filter_out                   false
% 3.06/1.01  --pred_elim                             true
% 3.06/1.01  --res_sim_input                         true
% 3.06/1.01  --eq_ax_congr_red                       true
% 3.06/1.01  --pure_diseq_elim                       true
% 3.06/1.01  --brand_transform                       false
% 3.06/1.01  --non_eq_to_eq                          false
% 3.06/1.01  --prep_def_merge                        true
% 3.06/1.01  --prep_def_merge_prop_impl              false
% 3.06/1.02  --prep_def_merge_mbd                    true
% 3.06/1.02  --prep_def_merge_tr_red                 false
% 3.06/1.02  --prep_def_merge_tr_cl                  false
% 3.06/1.02  --smt_preprocessing                     true
% 3.06/1.02  --smt_ac_axioms                         fast
% 3.06/1.02  --preprocessed_out                      false
% 3.06/1.02  --preprocessed_stats                    false
% 3.06/1.02  
% 3.06/1.02  ------ Abstraction refinement Options
% 3.06/1.02  
% 3.06/1.02  --abstr_ref                             []
% 3.06/1.02  --abstr_ref_prep                        false
% 3.06/1.02  --abstr_ref_until_sat                   false
% 3.06/1.02  --abstr_ref_sig_restrict                funpre
% 3.06/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.02  --abstr_ref_under                       []
% 3.06/1.02  
% 3.06/1.02  ------ SAT Options
% 3.06/1.02  
% 3.06/1.02  --sat_mode                              false
% 3.06/1.02  --sat_fm_restart_options                ""
% 3.06/1.02  --sat_gr_def                            false
% 3.06/1.02  --sat_epr_types                         true
% 3.06/1.02  --sat_non_cyclic_types                  false
% 3.06/1.02  --sat_finite_models                     false
% 3.06/1.02  --sat_fm_lemmas                         false
% 3.06/1.02  --sat_fm_prep                           false
% 3.06/1.02  --sat_fm_uc_incr                        true
% 3.06/1.02  --sat_out_model                         small
% 3.06/1.02  --sat_out_clauses                       false
% 3.06/1.02  
% 3.06/1.02  ------ QBF Options
% 3.06/1.02  
% 3.06/1.02  --qbf_mode                              false
% 3.06/1.02  --qbf_elim_univ                         false
% 3.06/1.02  --qbf_dom_inst                          none
% 3.06/1.02  --qbf_dom_pre_inst                      false
% 3.06/1.02  --qbf_sk_in                             false
% 3.06/1.02  --qbf_pred_elim                         true
% 3.06/1.02  --qbf_split                             512
% 3.06/1.02  
% 3.06/1.02  ------ BMC1 Options
% 3.06/1.02  
% 3.06/1.02  --bmc1_incremental                      false
% 3.06/1.02  --bmc1_axioms                           reachable_all
% 3.06/1.02  --bmc1_min_bound                        0
% 3.06/1.02  --bmc1_max_bound                        -1
% 3.06/1.02  --bmc1_max_bound_default                -1
% 3.06/1.02  --bmc1_symbol_reachability              true
% 3.06/1.02  --bmc1_property_lemmas                  false
% 3.06/1.02  --bmc1_k_induction                      false
% 3.06/1.02  --bmc1_non_equiv_states                 false
% 3.06/1.02  --bmc1_deadlock                         false
% 3.06/1.02  --bmc1_ucm                              false
% 3.06/1.02  --bmc1_add_unsat_core                   none
% 3.06/1.02  --bmc1_unsat_core_children              false
% 3.06/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.02  --bmc1_out_stat                         full
% 3.06/1.02  --bmc1_ground_init                      false
% 3.06/1.02  --bmc1_pre_inst_next_state              false
% 3.06/1.02  --bmc1_pre_inst_state                   false
% 3.06/1.02  --bmc1_pre_inst_reach_state             false
% 3.06/1.02  --bmc1_out_unsat_core                   false
% 3.06/1.02  --bmc1_aig_witness_out                  false
% 3.06/1.02  --bmc1_verbose                          false
% 3.06/1.02  --bmc1_dump_clauses_tptp                false
% 3.06/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.02  --bmc1_dump_file                        -
% 3.06/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.02  --bmc1_ucm_extend_mode                  1
% 3.06/1.02  --bmc1_ucm_init_mode                    2
% 3.06/1.02  --bmc1_ucm_cone_mode                    none
% 3.06/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.02  --bmc1_ucm_relax_model                  4
% 3.06/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.02  --bmc1_ucm_layered_model                none
% 3.06/1.02  --bmc1_ucm_max_lemma_size               10
% 3.06/1.02  
% 3.06/1.02  ------ AIG Options
% 3.06/1.02  
% 3.06/1.02  --aig_mode                              false
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation Options
% 3.06/1.02  
% 3.06/1.02  --instantiation_flag                    true
% 3.06/1.02  --inst_sos_flag                         true
% 3.06/1.02  --inst_sos_phase                        true
% 3.06/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel_side                     num_symb
% 3.06/1.02  --inst_solver_per_active                1400
% 3.06/1.02  --inst_solver_calls_frac                1.
% 3.06/1.02  --inst_passive_queue_type               priority_queues
% 3.06/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.02  --inst_passive_queues_freq              [25;2]
% 3.06/1.02  --inst_dismatching                      true
% 3.06/1.02  --inst_eager_unprocessed_to_passive     true
% 3.06/1.02  --inst_prop_sim_given                   true
% 3.06/1.02  --inst_prop_sim_new                     false
% 3.06/1.02  --inst_subs_new                         false
% 3.06/1.02  --inst_eq_res_simp                      false
% 3.06/1.02  --inst_subs_given                       false
% 3.06/1.02  --inst_orphan_elimination               true
% 3.06/1.02  --inst_learning_loop_flag               true
% 3.06/1.02  --inst_learning_start                   3000
% 3.06/1.02  --inst_learning_factor                  2
% 3.06/1.02  --inst_start_prop_sim_after_learn       3
% 3.06/1.02  --inst_sel_renew                        solver
% 3.06/1.02  --inst_lit_activity_flag                true
% 3.06/1.02  --inst_restr_to_given                   false
% 3.06/1.02  --inst_activity_threshold               500
% 3.06/1.02  --inst_out_proof                        true
% 3.06/1.02  
% 3.06/1.02  ------ Resolution Options
% 3.06/1.02  
% 3.06/1.02  --resolution_flag                       true
% 3.06/1.02  --res_lit_sel                           adaptive
% 3.06/1.02  --res_lit_sel_side                      none
% 3.06/1.02  --res_ordering                          kbo
% 3.06/1.02  --res_to_prop_solver                    active
% 3.06/1.02  --res_prop_simpl_new                    false
% 3.06/1.02  --res_prop_simpl_given                  true
% 3.06/1.02  --res_passive_queue_type                priority_queues
% 3.06/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.02  --res_passive_queues_freq               [15;5]
% 3.06/1.02  --res_forward_subs                      full
% 3.06/1.02  --res_backward_subs                     full
% 3.06/1.02  --res_forward_subs_resolution           true
% 3.06/1.02  --res_backward_subs_resolution          true
% 3.06/1.02  --res_orphan_elimination                true
% 3.06/1.02  --res_time_limit                        2.
% 3.06/1.02  --res_out_proof                         true
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Options
% 3.06/1.02  
% 3.06/1.02  --superposition_flag                    true
% 3.06/1.02  --sup_passive_queue_type                priority_queues
% 3.06/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.02  --demod_completeness_check              fast
% 3.06/1.02  --demod_use_ground                      true
% 3.06/1.02  --sup_to_prop_solver                    passive
% 3.06/1.02  --sup_prop_simpl_new                    true
% 3.06/1.02  --sup_prop_simpl_given                  true
% 3.06/1.02  --sup_fun_splitting                     true
% 3.06/1.02  --sup_smt_interval                      50000
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Simplification Setup
% 3.06/1.02  
% 3.06/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.06/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.06/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.06/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.06/1.02  --sup_immed_triv                        [TrivRules]
% 3.06/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_bw_main                     []
% 3.06/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.06/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_input_bw                          []
% 3.06/1.02  
% 3.06/1.02  ------ Combination Options
% 3.06/1.02  
% 3.06/1.02  --comb_res_mult                         3
% 3.06/1.02  --comb_sup_mult                         2
% 3.06/1.02  --comb_inst_mult                        10
% 3.06/1.02  
% 3.06/1.02  ------ Debug Options
% 3.06/1.02  
% 3.06/1.02  --dbg_backtrace                         false
% 3.06/1.02  --dbg_dump_prop_clauses                 false
% 3.06/1.02  --dbg_dump_prop_clauses_file            -
% 3.06/1.02  --dbg_out_stat                          false
% 3.06/1.02  ------ Parsing...
% 3.06/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.02  ------ Proving...
% 3.06/1.02  ------ Problem Properties 
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  clauses                                 28
% 3.06/1.02  conjectures                             5
% 3.06/1.02  EPR                                     8
% 3.06/1.02  Horn                                    24
% 3.06/1.02  unary                                   6
% 3.06/1.02  binary                                  11
% 3.06/1.02  lits                                    61
% 3.06/1.02  lits eq                                 8
% 3.06/1.02  fd_pure                                 0
% 3.06/1.02  fd_pseudo                               0
% 3.06/1.02  fd_cond                                 1
% 3.06/1.02  fd_pseudo_cond                          0
% 3.06/1.02  AC symbols                              0
% 3.06/1.02  
% 3.06/1.02  ------ Schedule dynamic 5 is on 
% 3.06/1.02  
% 3.06/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  ------ 
% 3.06/1.02  Current options:
% 3.06/1.02  ------ 
% 3.06/1.02  
% 3.06/1.02  ------ Input Options
% 3.06/1.02  
% 3.06/1.02  --out_options                           all
% 3.06/1.02  --tptp_safe_out                         true
% 3.06/1.02  --problem_path                          ""
% 3.06/1.02  --include_path                          ""
% 3.06/1.02  --clausifier                            res/vclausify_rel
% 3.06/1.02  --clausifier_options                    ""
% 3.06/1.02  --stdin                                 false
% 3.06/1.02  --stats_out                             all
% 3.06/1.02  
% 3.06/1.02  ------ General Options
% 3.06/1.02  
% 3.06/1.02  --fof                                   false
% 3.06/1.02  --time_out_real                         305.
% 3.06/1.02  --time_out_virtual                      -1.
% 3.06/1.02  --symbol_type_check                     false
% 3.06/1.02  --clausify_out                          false
% 3.06/1.02  --sig_cnt_out                           false
% 3.06/1.02  --trig_cnt_out                          false
% 3.06/1.02  --trig_cnt_out_tolerance                1.
% 3.06/1.02  --trig_cnt_out_sk_spl                   false
% 3.06/1.02  --abstr_cl_out                          false
% 3.06/1.02  
% 3.06/1.02  ------ Global Options
% 3.06/1.02  
% 3.06/1.02  --schedule                              default
% 3.06/1.02  --add_important_lit                     false
% 3.06/1.02  --prop_solver_per_cl                    1000
% 3.06/1.02  --min_unsat_core                        false
% 3.06/1.02  --soft_assumptions                      false
% 3.06/1.02  --soft_lemma_size                       3
% 3.06/1.02  --prop_impl_unit_size                   0
% 3.06/1.02  --prop_impl_unit                        []
% 3.06/1.02  --share_sel_clauses                     true
% 3.06/1.02  --reset_solvers                         false
% 3.06/1.02  --bc_imp_inh                            [conj_cone]
% 3.06/1.02  --conj_cone_tolerance                   3.
% 3.06/1.02  --extra_neg_conj                        none
% 3.06/1.02  --large_theory_mode                     true
% 3.06/1.02  --prolific_symb_bound                   200
% 3.06/1.02  --lt_threshold                          2000
% 3.06/1.02  --clause_weak_htbl                      true
% 3.06/1.02  --gc_record_bc_elim                     false
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing Options
% 3.06/1.02  
% 3.06/1.02  --preprocessing_flag                    true
% 3.06/1.02  --time_out_prep_mult                    0.1
% 3.06/1.02  --splitting_mode                        input
% 3.06/1.02  --splitting_grd                         true
% 3.06/1.02  --splitting_cvd                         false
% 3.06/1.02  --splitting_cvd_svl                     false
% 3.06/1.02  --splitting_nvd                         32
% 3.06/1.02  --sub_typing                            true
% 3.06/1.02  --prep_gs_sim                           true
% 3.06/1.02  --prep_unflatten                        true
% 3.06/1.02  --prep_res_sim                          true
% 3.06/1.02  --prep_upred                            true
% 3.06/1.02  --prep_sem_filter                       exhaustive
% 3.06/1.02  --prep_sem_filter_out                   false
% 3.06/1.02  --pred_elim                             true
% 3.06/1.02  --res_sim_input                         true
% 3.06/1.02  --eq_ax_congr_red                       true
% 3.06/1.02  --pure_diseq_elim                       true
% 3.06/1.02  --brand_transform                       false
% 3.06/1.02  --non_eq_to_eq                          false
% 3.06/1.02  --prep_def_merge                        true
% 3.06/1.02  --prep_def_merge_prop_impl              false
% 3.06/1.02  --prep_def_merge_mbd                    true
% 3.06/1.02  --prep_def_merge_tr_red                 false
% 3.06/1.02  --prep_def_merge_tr_cl                  false
% 3.06/1.02  --smt_preprocessing                     true
% 3.06/1.02  --smt_ac_axioms                         fast
% 3.06/1.02  --preprocessed_out                      false
% 3.06/1.02  --preprocessed_stats                    false
% 3.06/1.02  
% 3.06/1.02  ------ Abstraction refinement Options
% 3.06/1.02  
% 3.06/1.02  --abstr_ref                             []
% 3.06/1.02  --abstr_ref_prep                        false
% 3.06/1.02  --abstr_ref_until_sat                   false
% 3.06/1.02  --abstr_ref_sig_restrict                funpre
% 3.06/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.02  --abstr_ref_under                       []
% 3.06/1.02  
% 3.06/1.02  ------ SAT Options
% 3.06/1.02  
% 3.06/1.02  --sat_mode                              false
% 3.06/1.02  --sat_fm_restart_options                ""
% 3.06/1.02  --sat_gr_def                            false
% 3.06/1.02  --sat_epr_types                         true
% 3.06/1.02  --sat_non_cyclic_types                  false
% 3.06/1.02  --sat_finite_models                     false
% 3.06/1.02  --sat_fm_lemmas                         false
% 3.06/1.02  --sat_fm_prep                           false
% 3.06/1.02  --sat_fm_uc_incr                        true
% 3.06/1.02  --sat_out_model                         small
% 3.06/1.02  --sat_out_clauses                       false
% 3.06/1.02  
% 3.06/1.02  ------ QBF Options
% 3.06/1.02  
% 3.06/1.02  --qbf_mode                              false
% 3.06/1.02  --qbf_elim_univ                         false
% 3.06/1.02  --qbf_dom_inst                          none
% 3.06/1.02  --qbf_dom_pre_inst                      false
% 3.06/1.02  --qbf_sk_in                             false
% 3.06/1.02  --qbf_pred_elim                         true
% 3.06/1.02  --qbf_split                             512
% 3.06/1.02  
% 3.06/1.02  ------ BMC1 Options
% 3.06/1.02  
% 3.06/1.02  --bmc1_incremental                      false
% 3.06/1.02  --bmc1_axioms                           reachable_all
% 3.06/1.02  --bmc1_min_bound                        0
% 3.06/1.02  --bmc1_max_bound                        -1
% 3.06/1.02  --bmc1_max_bound_default                -1
% 3.06/1.02  --bmc1_symbol_reachability              true
% 3.06/1.02  --bmc1_property_lemmas                  false
% 3.06/1.02  --bmc1_k_induction                      false
% 3.06/1.02  --bmc1_non_equiv_states                 false
% 3.06/1.02  --bmc1_deadlock                         false
% 3.06/1.02  --bmc1_ucm                              false
% 3.06/1.02  --bmc1_add_unsat_core                   none
% 3.06/1.02  --bmc1_unsat_core_children              false
% 3.06/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.02  --bmc1_out_stat                         full
% 3.06/1.02  --bmc1_ground_init                      false
% 3.06/1.02  --bmc1_pre_inst_next_state              false
% 3.06/1.02  --bmc1_pre_inst_state                   false
% 3.06/1.02  --bmc1_pre_inst_reach_state             false
% 3.06/1.02  --bmc1_out_unsat_core                   false
% 3.06/1.02  --bmc1_aig_witness_out                  false
% 3.06/1.02  --bmc1_verbose                          false
% 3.06/1.02  --bmc1_dump_clauses_tptp                false
% 3.06/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.02  --bmc1_dump_file                        -
% 3.06/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.02  --bmc1_ucm_extend_mode                  1
% 3.06/1.02  --bmc1_ucm_init_mode                    2
% 3.06/1.02  --bmc1_ucm_cone_mode                    none
% 3.06/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.02  --bmc1_ucm_relax_model                  4
% 3.06/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.02  --bmc1_ucm_layered_model                none
% 3.06/1.02  --bmc1_ucm_max_lemma_size               10
% 3.06/1.02  
% 3.06/1.02  ------ AIG Options
% 3.06/1.02  
% 3.06/1.02  --aig_mode                              false
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation Options
% 3.06/1.02  
% 3.06/1.02  --instantiation_flag                    true
% 3.06/1.02  --inst_sos_flag                         true
% 3.06/1.02  --inst_sos_phase                        true
% 3.06/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel_side                     none
% 3.06/1.02  --inst_solver_per_active                1400
% 3.06/1.02  --inst_solver_calls_frac                1.
% 3.06/1.02  --inst_passive_queue_type               priority_queues
% 3.06/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.02  --inst_passive_queues_freq              [25;2]
% 3.06/1.02  --inst_dismatching                      true
% 3.06/1.02  --inst_eager_unprocessed_to_passive     true
% 3.06/1.02  --inst_prop_sim_given                   true
% 3.06/1.02  --inst_prop_sim_new                     false
% 3.06/1.02  --inst_subs_new                         false
% 3.06/1.02  --inst_eq_res_simp                      false
% 3.06/1.02  --inst_subs_given                       false
% 3.06/1.02  --inst_orphan_elimination               true
% 3.06/1.02  --inst_learning_loop_flag               true
% 3.06/1.02  --inst_learning_start                   3000
% 3.06/1.02  --inst_learning_factor                  2
% 3.06/1.02  --inst_start_prop_sim_after_learn       3
% 3.06/1.02  --inst_sel_renew                        solver
% 3.06/1.02  --inst_lit_activity_flag                true
% 3.06/1.02  --inst_restr_to_given                   false
% 3.06/1.02  --inst_activity_threshold               500
% 3.06/1.02  --inst_out_proof                        true
% 3.06/1.02  
% 3.06/1.02  ------ Resolution Options
% 3.06/1.02  
% 3.06/1.02  --resolution_flag                       false
% 3.06/1.02  --res_lit_sel                           adaptive
% 3.06/1.02  --res_lit_sel_side                      none
% 3.06/1.02  --res_ordering                          kbo
% 3.06/1.02  --res_to_prop_solver                    active
% 3.06/1.02  --res_prop_simpl_new                    false
% 3.06/1.02  --res_prop_simpl_given                  true
% 3.06/1.02  --res_passive_queue_type                priority_queues
% 3.06/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.02  --res_passive_queues_freq               [15;5]
% 3.06/1.02  --res_forward_subs                      full
% 3.06/1.02  --res_backward_subs                     full
% 3.06/1.02  --res_forward_subs_resolution           true
% 3.06/1.02  --res_backward_subs_resolution          true
% 3.06/1.02  --res_orphan_elimination                true
% 3.06/1.02  --res_time_limit                        2.
% 3.06/1.02  --res_out_proof                         true
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Options
% 3.06/1.02  
% 3.06/1.02  --superposition_flag                    true
% 3.06/1.02  --sup_passive_queue_type                priority_queues
% 3.06/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.02  --demod_completeness_check              fast
% 3.06/1.02  --demod_use_ground                      true
% 3.06/1.02  --sup_to_prop_solver                    passive
% 3.06/1.02  --sup_prop_simpl_new                    true
% 3.06/1.02  --sup_prop_simpl_given                  true
% 3.06/1.02  --sup_fun_splitting                     true
% 3.06/1.02  --sup_smt_interval                      50000
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Simplification Setup
% 3.06/1.02  
% 3.06/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.06/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.06/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.06/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.06/1.02  --sup_immed_triv                        [TrivRules]
% 3.06/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_bw_main                     []
% 3.06/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.06/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_input_bw                          []
% 3.06/1.02  
% 3.06/1.02  ------ Combination Options
% 3.06/1.02  
% 3.06/1.02  --comb_res_mult                         3
% 3.06/1.02  --comb_sup_mult                         2
% 3.06/1.02  --comb_inst_mult                        10
% 3.06/1.02  
% 3.06/1.02  ------ Debug Options
% 3.06/1.02  
% 3.06/1.02  --dbg_backtrace                         false
% 3.06/1.02  --dbg_dump_prop_clauses                 false
% 3.06/1.02  --dbg_dump_prop_clauses_file            -
% 3.06/1.02  --dbg_out_stat                          false
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  ------ Proving...
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  % SZS status Theorem for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  fof(f5,axiom,(
% 3.06/1.02    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f47,plain,(
% 3.06/1.02    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f48,plain,(
% 3.06/1.02    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f47])).
% 3.06/1.02  
% 3.06/1.02  fof(f64,plain,(
% 3.06/1.02    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f48])).
% 3.06/1.02  
% 3.06/1.02  fof(f7,axiom,(
% 3.06/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f27,plain,(
% 3.06/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f7])).
% 3.06/1.02  
% 3.06/1.02  fof(f28,plain,(
% 3.06/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.06/1.02    inference(flattening,[],[f27])).
% 3.06/1.02  
% 3.06/1.02  fof(f66,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f28])).
% 3.06/1.02  
% 3.06/1.02  fof(f3,axiom,(
% 3.06/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f20,plain,(
% 3.06/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.06/1.02    inference(rectify,[],[f3])).
% 3.06/1.02  
% 3.06/1.02  fof(f23,plain,(
% 3.06/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.06/1.02    inference(ennf_transformation,[],[f20])).
% 3.06/1.02  
% 3.06/1.02  fof(f45,plain,(
% 3.06/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f46,plain,(
% 3.06/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f45])).
% 3.06/1.02  
% 3.06/1.02  fof(f61,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f46])).
% 3.06/1.02  
% 3.06/1.02  fof(f6,axiom,(
% 3.06/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f26,plain,(
% 3.06/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f6])).
% 3.06/1.02  
% 3.06/1.02  fof(f65,plain,(
% 3.06/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f26])).
% 3.06/1.02  
% 3.06/1.02  fof(f18,conjecture,(
% 3.06/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f19,negated_conjecture,(
% 3.06/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 3.06/1.02    inference(negated_conjecture,[],[f18])).
% 3.06/1.02  
% 3.06/1.02  fof(f39,plain,(
% 3.06/1.02    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.06/1.02    inference(ennf_transformation,[],[f19])).
% 3.06/1.02  
% 3.06/1.02  fof(f40,plain,(
% 3.06/1.02    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.06/1.02    inference(flattening,[],[f39])).
% 3.06/1.02  
% 3.06/1.02  fof(f54,plain,(
% 3.06/1.02    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK5)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f53,plain,(
% 3.06/1.02    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK4,X2)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(X0,sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK4)))) & ~v1_xboole_0(sK4))) )),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f52,plain,(
% 3.06/1.02    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK3,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f55,plain,(
% 3.06/1.02    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f54,f53,f52])).
% 3.06/1.02  
% 3.06/1.02  fof(f83,plain,(
% 3.06/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.06/1.02    inference(cnf_transformation,[],[f55])).
% 3.06/1.02  
% 3.06/1.02  fof(f17,axiom,(
% 3.06/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f38,plain,(
% 3.06/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.02    inference(ennf_transformation,[],[f17])).
% 3.06/1.02  
% 3.06/1.02  fof(f80,plain,(
% 3.06/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.02    inference(cnf_transformation,[],[f38])).
% 3.06/1.02  
% 3.06/1.02  fof(f60,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f46])).
% 3.06/1.02  
% 3.06/1.02  fof(f85,plain,(
% 3.06/1.02    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f55])).
% 3.06/1.02  
% 3.06/1.02  fof(f4,axiom,(
% 3.06/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f24,plain,(
% 3.06/1.02    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f4])).
% 3.06/1.02  
% 3.06/1.02  fof(f25,plain,(
% 3.06/1.02    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.06/1.02    inference(flattening,[],[f24])).
% 3.06/1.02  
% 3.06/1.02  fof(f63,plain,(
% 3.06/1.02    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f25])).
% 3.06/1.02  
% 3.06/1.02  fof(f15,axiom,(
% 3.06/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f36,plain,(
% 3.06/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.02    inference(ennf_transformation,[],[f15])).
% 3.06/1.02  
% 3.06/1.02  fof(f78,plain,(
% 3.06/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.02    inference(cnf_transformation,[],[f36])).
% 3.06/1.02  
% 3.06/1.02  fof(f10,axiom,(
% 3.06/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f31,plain,(
% 3.06/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f10])).
% 3.06/1.02  
% 3.06/1.02  fof(f50,plain,(
% 3.06/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(nnf_transformation,[],[f31])).
% 3.06/1.02  
% 3.06/1.02  fof(f70,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f50])).
% 3.06/1.02  
% 3.06/1.02  fof(f11,axiom,(
% 3.06/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f72,plain,(
% 3.06/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.06/1.02    inference(cnf_transformation,[],[f11])).
% 3.06/1.02  
% 3.06/1.02  fof(f8,axiom,(
% 3.06/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f29,plain,(
% 3.06/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.06/1.02    inference(ennf_transformation,[],[f8])).
% 3.06/1.02  
% 3.06/1.02  fof(f67,plain,(
% 3.06/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f29])).
% 3.06/1.02  
% 3.06/1.02  fof(f2,axiom,(
% 3.06/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f22,plain,(
% 3.06/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.06/1.02    inference(ennf_transformation,[],[f2])).
% 3.06/1.02  
% 3.06/1.02  fof(f59,plain,(
% 3.06/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f22])).
% 3.06/1.02  
% 3.06/1.02  fof(f1,axiom,(
% 3.06/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f21,plain,(
% 3.06/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.06/1.02    inference(ennf_transformation,[],[f1])).
% 3.06/1.02  
% 3.06/1.02  fof(f41,plain,(
% 3.06/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.02    inference(nnf_transformation,[],[f21])).
% 3.06/1.02  
% 3.06/1.02  fof(f42,plain,(
% 3.06/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.02    inference(rectify,[],[f41])).
% 3.06/1.02  
% 3.06/1.02  fof(f43,plain,(
% 3.06/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f44,plain,(
% 3.06/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.06/1.02  
% 3.06/1.02  fof(f57,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f44])).
% 3.06/1.02  
% 3.06/1.02  fof(f58,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f44])).
% 3.06/1.02  
% 3.06/1.02  fof(f9,axiom,(
% 3.06/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f30,plain,(
% 3.06/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f9])).
% 3.06/1.02  
% 3.06/1.02  fof(f49,plain,(
% 3.06/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(nnf_transformation,[],[f30])).
% 3.06/1.02  
% 3.06/1.02  fof(f69,plain,(
% 3.06/1.02    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f49])).
% 3.06/1.02  
% 3.06/1.02  fof(f14,axiom,(
% 3.06/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f34,plain,(
% 3.06/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.06/1.02    inference(ennf_transformation,[],[f14])).
% 3.06/1.02  
% 3.06/1.02  fof(f35,plain,(
% 3.06/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(flattening,[],[f34])).
% 3.06/1.02  
% 3.06/1.02  fof(f76,plain,(
% 3.06/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f35])).
% 3.06/1.02  
% 3.06/1.02  fof(f12,axiom,(
% 3.06/1.02    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f32,plain,(
% 3.06/1.02    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f12])).
% 3.06/1.02  
% 3.06/1.02  fof(f73,plain,(
% 3.06/1.02    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f32])).
% 3.06/1.02  
% 3.06/1.02  fof(f13,axiom,(
% 3.06/1.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f33,plain,(
% 3.06/1.02    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f13])).
% 3.06/1.02  
% 3.06/1.02  fof(f51,plain,(
% 3.06/1.02    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.06/1.02    inference(nnf_transformation,[],[f33])).
% 3.06/1.02  
% 3.06/1.02  fof(f74,plain,(
% 3.06/1.02    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f51])).
% 3.06/1.02  
% 3.06/1.02  fof(f62,plain,(
% 3.06/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f46])).
% 3.06/1.02  
% 3.06/1.02  fof(f16,axiom,(
% 3.06/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f37,plain,(
% 3.06/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.02    inference(ennf_transformation,[],[f16])).
% 3.06/1.02  
% 3.06/1.02  fof(f79,plain,(
% 3.06/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.02    inference(cnf_transformation,[],[f37])).
% 3.06/1.02  
% 3.06/1.02  fof(f84,plain,(
% 3.06/1.02    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)),
% 3.06/1.02    inference(cnf_transformation,[],[f55])).
% 3.06/1.02  
% 3.06/1.02  cnf(c_8,plain,
% 3.06/1.02      ( m1_subset_1(sK2(X0),X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2486,plain,
% 3.06/1.02      ( m1_subset_1(sK2(X0),X0) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_10,plain,
% 3.06/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2484,plain,
% 3.06/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X0,X1) = iProver_top
% 3.06/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3582,plain,
% 3.06/1.02      ( r2_hidden(sK2(X0),X0) = iProver_top
% 3.06/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2486,c_2484]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2489,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) = iProver_top
% 3.06/1.02      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_9,plain,
% 3.06/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2485,plain,
% 3.06/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 3.06/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2983,plain,
% 3.06/1.02      ( m1_subset_1(sK1(X0,X1),X1) = iProver_top
% 3.06/1.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2489,c_2485]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_27,negated_conjecture,
% 3.06/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.06/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2471,plain,
% 3.06/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_24,plain,
% 3.06/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2473,plain,
% 3.06/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.06/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3479,plain,
% 3.06/1.02      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2471,c_2473]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_6,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2488,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) = iProver_top
% 3.06/1.02      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_25,negated_conjecture,
% 3.06/1.02      ( ~ m1_subset_1(X0,sK4)
% 3.06/1.02      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
% 3.06/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2472,plain,
% 3.06/1.02      ( m1_subset_1(X0,sK4) != iProver_top
% 3.06/1.02      | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2975,plain,
% 3.06/1.02      ( m1_subset_1(sK1(k2_relset_1(sK3,sK4,sK5),X0),sK4) != iProver_top
% 3.06/1.02      | r1_xboole_0(k2_relset_1(sK3,sK4,sK5),X0) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2488,c_2472]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3658,plain,
% 3.06/1.02      ( m1_subset_1(sK1(k2_relat_1(sK5),X0),sK4) != iProver_top
% 3.06/1.02      | r1_xboole_0(k2_relat_1(sK5),X0) = iProver_top ),
% 3.06/1.02      inference(demodulation,[status(thm)],[c_3479,c_2975]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5337,plain,
% 3.06/1.02      ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2983,c_3658]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_7,plain,
% 3.06/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2487,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 3.06/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.06/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5554,plain,
% 3.06/1.02      ( r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
% 3.06/1.02      | v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_5337,c_2487]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_21,plain,
% 3.06/1.02      ( v5_relat_1(X0,X1)
% 3.06/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.06/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_15,plain,
% 3.06/1.02      ( ~ v5_relat_1(X0,X1)
% 3.06/1.02      | r1_tarski(k2_relat_1(X0),X1)
% 3.06/1.02      | ~ v1_relat_1(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_332,plain,
% 3.06/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 3.06/1.02      | ~ v1_relat_1(X0) ),
% 3.06/1.02      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2468,plain,
% 3.06/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/1.02      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2908,plain,
% 3.06/1.02      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.06/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2471,c_2468]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_16,plain,
% 3.06/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.06/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2480,plain,
% 3.06/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_11,plain,
% 3.06/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.02      | ~ v1_relat_1(X1)
% 3.06/1.02      | v1_relat_1(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2483,plain,
% 3.06/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/1.02      | v1_relat_1(X1) != iProver_top
% 3.06/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3956,plain,
% 3.06/1.02      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.06/1.02      | v1_relat_1(sK5) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2471,c_2483]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4128,plain,
% 3.06/1.02      ( v1_relat_1(sK5) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2480,c_3956]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5612,plain,
% 3.06/1.02      ( v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(global_propositional_subsumption,
% 3.06/1.02                [status(thm)],
% 3.06/1.02                [c_5554,c_2908,c_4128]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3,plain,
% 3.06/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.06/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2491,plain,
% 3.06/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5616,plain,
% 3.06/1.02      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_5612,c_2491]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_1,plain,
% 3.06/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2493,plain,
% 3.06/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.06/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_0,plain,
% 3.06/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2494,plain,
% 3.06/1.02      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.06/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3373,plain,
% 3.06/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2493,c_2494]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_12,plain,
% 3.06/1.02      ( v4_relat_1(X0,X1)
% 3.06/1.02      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.06/1.02      | ~ v1_relat_1(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2482,plain,
% 3.06/1.02      ( v4_relat_1(X0,X1) = iProver_top
% 3.06/1.02      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4604,plain,
% 3.06/1.02      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_3373,c_2482]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_20,plain,
% 3.06/1.02      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.06/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2476,plain,
% 3.06/1.02      ( k7_relat_1(X0,X1) = X0
% 3.06/1.02      | v4_relat_1(X0,X1) != iProver_top
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4994,plain,
% 3.06/1.02      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_4604,c_2476]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5052,plain,
% 3.06/1.02      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_4128,c_4994]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_17,plain,
% 3.06/1.02      ( ~ v1_relat_1(X0)
% 3.06/1.02      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2479,plain,
% 3.06/1.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4271,plain,
% 3.06/1.02      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_4128,c_2479]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5057,plain,
% 3.06/1.02      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_5052,c_4271]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_19,plain,
% 3.06/1.02      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.06/1.02      | ~ v1_relat_1(X0)
% 3.06/1.02      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 3.06/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2477,plain,
% 3.06/1.02      ( k9_relat_1(X0,X1) != k1_xboole_0
% 3.06/1.02      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 3.06/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5129,plain,
% 3.06/1.02      ( k2_relat_1(sK5) != k1_xboole_0
% 3.06/1.02      | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_5057,c_2477]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5132,plain,
% 3.06/1.02      ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
% 3.06/1.02      | k2_relat_1(sK5) != k1_xboole_0 ),
% 3.06/1.02      inference(global_propositional_subsumption,
% 3.06/1.02                [status(thm)],
% 3.06/1.02                [c_5129,c_4128]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5133,plain,
% 3.06/1.02      ( k2_relat_1(sK5) != k1_xboole_0
% 3.06/1.02      | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(renaming,[status(thm)],[c_5132]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5715,plain,
% 3.06/1.02      ( k1_xboole_0 != k1_xboole_0
% 3.06/1.02      | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(demodulation,[status(thm)],[c_5616,c_5133]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_5726,plain,
% 3.06/1.02      ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(equality_resolution_simp,[status(thm)],[c_5715]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4,plain,
% 3.06/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2490,plain,
% 3.06/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X2,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X2,X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_7591,plain,
% 3.06/1.02      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_5726,c_2490]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_8271,plain,
% 3.06/1.02      ( v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_3582,c_7591]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_9958,plain,
% 3.06/1.02      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_8271,c_2491]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_23,plain,
% 3.06/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_2474,plain,
% 3.06/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3532,plain,
% 3.06/1.02      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_2471,c_2474]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_26,negated_conjecture,
% 3.06/1.02      ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
% 3.06/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3730,plain,
% 3.06/1.02      ( k1_relat_1(sK5) != k1_xboole_0 ),
% 3.06/1.02      inference(demodulation,[status(thm)],[c_3532,c_26]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(contradiction,plain,
% 3.06/1.02      ( $false ),
% 3.06/1.02      inference(minisat,[status(thm)],[c_9958,c_3730]) ).
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  ------                               Statistics
% 3.06/1.02  
% 3.06/1.02  ------ General
% 3.06/1.02  
% 3.06/1.02  abstr_ref_over_cycles:                  0
% 3.06/1.02  abstr_ref_under_cycles:                 0
% 3.06/1.02  gc_basic_clause_elim:                   0
% 3.06/1.02  forced_gc_time:                         0
% 3.06/1.02  parsing_time:                           0.008
% 3.06/1.02  unif_index_cands_time:                  0.
% 3.06/1.02  unif_index_add_time:                    0.
% 3.06/1.02  orderings_time:                         0.
% 3.06/1.02  out_proof_time:                         0.009
% 3.06/1.02  total_time:                             0.291
% 3.06/1.02  num_of_symbols:                         54
% 3.06/1.02  num_of_terms:                           7177
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing
% 3.06/1.02  
% 3.06/1.02  num_of_splits:                          0
% 3.06/1.02  num_of_split_atoms:                     0
% 3.06/1.02  num_of_reused_defs:                     0
% 3.06/1.02  num_eq_ax_congr_red:                    44
% 3.06/1.02  num_of_sem_filtered_clauses:            1
% 3.06/1.02  num_of_subtypes:                        0
% 3.06/1.02  monotx_restored_types:                  0
% 3.06/1.02  sat_num_of_epr_types:                   0
% 3.06/1.02  sat_num_of_non_cyclic_types:            0
% 3.06/1.02  sat_guarded_non_collapsed_types:        0
% 3.06/1.02  num_pure_diseq_elim:                    0
% 3.06/1.02  simp_replaced_by:                       0
% 3.06/1.02  res_preprocessed:                       141
% 3.06/1.02  prep_upred:                             0
% 3.06/1.02  prep_unflattend:                        128
% 3.06/1.02  smt_new_axioms:                         0
% 3.06/1.02  pred_elim_cands:                        7
% 3.06/1.02  pred_elim:                              1
% 3.06/1.02  pred_elim_cl:                           2
% 3.06/1.02  pred_elim_cycles:                       11
% 3.06/1.02  merged_defs:                            0
% 3.06/1.02  merged_defs_ncl:                        0
% 3.06/1.02  bin_hyper_res:                          0
% 3.06/1.02  prep_cycles:                            4
% 3.06/1.02  pred_elim_time:                         0.014
% 3.06/1.02  splitting_time:                         0.
% 3.06/1.02  sem_filter_time:                        0.
% 3.06/1.02  monotx_time:                            0.
% 3.06/1.02  subtype_inf_time:                       0.
% 3.06/1.02  
% 3.06/1.02  ------ Problem properties
% 3.06/1.02  
% 3.06/1.02  clauses:                                28
% 3.06/1.02  conjectures:                            5
% 3.06/1.02  epr:                                    8
% 3.06/1.02  horn:                                   24
% 3.06/1.02  ground:                                 4
% 3.06/1.02  unary:                                  6
% 3.06/1.02  binary:                                 11
% 3.06/1.02  lits:                                   61
% 3.06/1.02  lits_eq:                                8
% 3.06/1.02  fd_pure:                                0
% 3.06/1.02  fd_pseudo:                              0
% 3.06/1.02  fd_cond:                                1
% 3.06/1.02  fd_pseudo_cond:                         0
% 3.06/1.02  ac_symbols:                             0
% 3.06/1.02  
% 3.06/1.02  ------ Propositional Solver
% 3.06/1.02  
% 3.06/1.02  prop_solver_calls:                      32
% 3.06/1.02  prop_fast_solver_calls:                 1223
% 3.06/1.02  smt_solver_calls:                       0
% 3.06/1.02  smt_fast_solver_calls:                  0
% 3.06/1.02  prop_num_of_clauses:                    3671
% 3.06/1.02  prop_preprocess_simplified:             10864
% 3.06/1.02  prop_fo_subsumed:                       13
% 3.06/1.02  prop_solver_time:                       0.
% 3.06/1.02  smt_solver_time:                        0.
% 3.06/1.02  smt_fast_solver_time:                   0.
% 3.06/1.02  prop_fast_solver_time:                  0.
% 3.06/1.02  prop_unsat_core_time:                   0.
% 3.06/1.02  
% 3.06/1.02  ------ QBF
% 3.06/1.02  
% 3.06/1.02  qbf_q_res:                              0
% 3.06/1.02  qbf_num_tautologies:                    0
% 3.06/1.02  qbf_prep_cycles:                        0
% 3.06/1.02  
% 3.06/1.02  ------ BMC1
% 3.06/1.02  
% 3.06/1.02  bmc1_current_bound:                     -1
% 3.06/1.02  bmc1_last_solved_bound:                 -1
% 3.06/1.02  bmc1_unsat_core_size:                   -1
% 3.06/1.02  bmc1_unsat_core_parents_size:           -1
% 3.06/1.02  bmc1_merge_next_fun:                    0
% 3.06/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation
% 3.06/1.02  
% 3.06/1.02  inst_num_of_clauses:                    1178
% 3.06/1.02  inst_num_in_passive:                    371
% 3.06/1.02  inst_num_in_active:                     643
% 3.06/1.02  inst_num_in_unprocessed:                164
% 3.06/1.02  inst_num_of_loops:                      710
% 3.06/1.02  inst_num_of_learning_restarts:          0
% 3.06/1.02  inst_num_moves_active_passive:          63
% 3.06/1.02  inst_lit_activity:                      0
% 3.06/1.02  inst_lit_activity_moves:                0
% 3.06/1.02  inst_num_tautologies:                   0
% 3.06/1.02  inst_num_prop_implied:                  0
% 3.06/1.02  inst_num_existing_simplified:           0
% 3.06/1.02  inst_num_eq_res_simplified:             0
% 3.06/1.02  inst_num_child_elim:                    0
% 3.06/1.02  inst_num_of_dismatching_blockings:      564
% 3.06/1.02  inst_num_of_non_proper_insts:           1304
% 3.06/1.02  inst_num_of_duplicates:                 0
% 3.06/1.02  inst_inst_num_from_inst_to_res:         0
% 3.06/1.02  inst_dismatching_checking_time:         0.
% 3.06/1.02  
% 3.06/1.02  ------ Resolution
% 3.06/1.02  
% 3.06/1.02  res_num_of_clauses:                     0
% 3.06/1.02  res_num_in_passive:                     0
% 3.06/1.02  res_num_in_active:                      0
% 3.06/1.02  res_num_of_loops:                       145
% 3.06/1.02  res_forward_subset_subsumed:            45
% 3.06/1.02  res_backward_subset_subsumed:           8
% 3.06/1.02  res_forward_subsumed:                   0
% 3.06/1.02  res_backward_subsumed:                  0
% 3.06/1.02  res_forward_subsumption_resolution:     0
% 3.06/1.02  res_backward_subsumption_resolution:    0
% 3.06/1.02  res_clause_to_clause_subsumption:       609
% 3.06/1.02  res_orphan_elimination:                 0
% 3.06/1.02  res_tautology_del:                      255
% 3.06/1.02  res_num_eq_res_simplified:              0
% 3.06/1.02  res_num_sel_changes:                    0
% 3.06/1.02  res_moves_from_active_to_pass:          0
% 3.06/1.02  
% 3.06/1.02  ------ Superposition
% 3.06/1.02  
% 3.06/1.02  sup_time_total:                         0.
% 3.06/1.02  sup_time_generating:                    0.
% 3.06/1.02  sup_time_sim_full:                      0.
% 3.06/1.02  sup_time_sim_immed:                     0.
% 3.06/1.02  
% 3.06/1.02  sup_num_of_clauses:                     163
% 3.06/1.02  sup_num_in_active:                      97
% 3.06/1.02  sup_num_in_passive:                     66
% 3.06/1.02  sup_num_of_loops:                       141
% 3.06/1.02  sup_fw_superposition:                   126
% 3.06/1.02  sup_bw_superposition:                   123
% 3.06/1.02  sup_immediate_simplified:               43
% 3.06/1.02  sup_given_eliminated:                   0
% 3.06/1.02  comparisons_done:                       0
% 3.06/1.02  comparisons_avoided:                    0
% 3.06/1.02  
% 3.06/1.02  ------ Simplifications
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  sim_fw_subset_subsumed:                 32
% 3.06/1.02  sim_bw_subset_subsumed:                 12
% 3.06/1.02  sim_fw_subsumed:                        10
% 3.06/1.02  sim_bw_subsumed:                        21
% 3.06/1.02  sim_fw_subsumption_res:                 0
% 3.06/1.02  sim_bw_subsumption_res:                 0
% 3.06/1.02  sim_tautology_del:                      2
% 3.06/1.02  sim_eq_tautology_del:                   2
% 3.06/1.02  sim_eq_res_simp:                        2
% 3.06/1.02  sim_fw_demodulated:                     0
% 3.06/1.02  sim_bw_demodulated:                     20
% 3.06/1.02  sim_light_normalised:                   2
% 3.06/1.02  sim_joinable_taut:                      0
% 3.06/1.02  sim_joinable_simp:                      0
% 3.06/1.02  sim_ac_normalised:                      0
% 3.06/1.02  sim_smt_subsumption:                    0
% 3.06/1.02  
%------------------------------------------------------------------------------
