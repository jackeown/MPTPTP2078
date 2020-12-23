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
% DateTime   : Thu Dec  3 11:56:46 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 216 expanded)
%              Number of clauses        :   61 (  75 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 ( 772 expanded)
%              Number of equality atoms :  103 ( 181 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k2_relset_1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,sK4))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(sK3,X0,X2))
                | ~ m1_subset_1(X3,sK3) )
            & k1_xboole_0 != k2_relset_1(sK3,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK2,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK2,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK3,sK2,sK4))
        | ~ m1_subset_1(X3,sK3) )
    & k1_xboole_0 != k2_relset_1(sK3,sK2,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f49,f48,f47])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK3,sK2,sK4))
      | ~ m1_subset_1(X3,sK3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_951,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_947,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_946,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_946,c_5])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_935,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | X5 != X1
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X3)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1988,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_932])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3033,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_944])).

cnf(c_3804,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_3033])).

cnf(c_4582,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_3804])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_938,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2971,plain,
    ( k1_relset_1(sK3,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_935,c_938])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_936,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1437,plain,
    ( m1_subset_1(sK0(k1_relset_1(sK3,sK2,sK4)),sK3) != iProver_top
    | v1_xboole_0(k1_relset_1(sK3,sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_936])).

cnf(c_3369,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4)),sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2971,c_1437])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_11])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_16,c_15,c_11])).

cnf(c_931,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1297,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_935,c_931])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_940,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3053,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_940])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1125,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_3681,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_27,c_1125])).

cnf(c_3682,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3681])).

cnf(c_3689,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4)),sK3) = iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_3682])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_945,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4590,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4)),sK3) = iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3689,c_945])).

cnf(c_4698,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4582,c_3369,c_4590])).

cnf(c_4705,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_4698])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_943,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_949,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1432,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_943,c_949])).

cnf(c_4913,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4705,c_1432])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_937,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2290,plain,
    ( k2_relset_1(sK3,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_935,c_937])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2595,plain,
    ( k2_relat_1(sK4) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2290,c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4913,c_2595])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n012.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.80/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.97  
% 2.80/0.97  ------  iProver source info
% 2.80/0.97  
% 2.80/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.97  git: non_committed_changes: false
% 2.80/0.97  git: last_make_outside_of_git: false
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     num_symb
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       true
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  ------ Parsing...
% 2.80/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.97  ------ Proving...
% 2.80/0.97  ------ Problem Properties 
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  clauses                                 23
% 2.80/0.97  conjectures                             5
% 2.80/0.97  EPR                                     6
% 2.80/0.97  Horn                                    22
% 2.80/0.97  unary                                   7
% 2.80/0.97  binary                                  11
% 2.80/0.97  lits                                    45
% 2.80/0.97  lits eq                                 6
% 2.80/0.97  fd_pure                                 0
% 2.80/0.97  fd_pseudo                               0
% 2.80/0.97  fd_cond                                 1
% 2.80/0.97  fd_pseudo_cond                          0
% 2.80/0.97  AC symbols                              0
% 2.80/0.97  
% 2.80/0.97  ------ Schedule dynamic 5 is on 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  Current options:
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     none
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       false
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ Proving...
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  % SZS status Theorem for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  fof(f1,axiom,(
% 2.80/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f39,plain,(
% 2.80/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.97    inference(nnf_transformation,[],[f1])).
% 2.80/0.97  
% 2.80/0.97  fof(f40,plain,(
% 2.80/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.97    inference(rectify,[],[f39])).
% 2.80/0.97  
% 2.80/0.97  fof(f41,plain,(
% 2.80/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f42,plain,(
% 2.80/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.80/0.97  
% 2.80/0.97  fof(f52,plain,(
% 2.80/0.97    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f42])).
% 2.80/0.97  
% 2.80/0.97  fof(f4,axiom,(
% 2.80/0.97    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f23,plain,(
% 2.80/0.97    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f4])).
% 2.80/0.97  
% 2.80/0.97  fof(f55,plain,(
% 2.80/0.97    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f23])).
% 2.80/0.97  
% 2.80/0.97  fof(f6,axiom,(
% 2.80/0.97    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f57,plain,(
% 2.80/0.97    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f6])).
% 2.80/0.97  
% 2.80/0.97  fof(f5,axiom,(
% 2.80/0.97    ! [X0] : k2_subset_1(X0) = X0),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f56,plain,(
% 2.80/0.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f5])).
% 2.80/0.97  
% 2.80/0.97  fof(f18,conjecture,(
% 2.80/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f19,negated_conjecture,(
% 2.80/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.80/0.97    inference(negated_conjecture,[],[f18])).
% 2.80/0.97  
% 2.80/0.97  fof(f37,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f19])).
% 2.80/0.97  
% 2.80/0.97  fof(f38,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.80/0.97    inference(flattening,[],[f37])).
% 2.80/0.97  
% 2.80/0.97  fof(f49,plain,(
% 2.80/0.97    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,sK4)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))) )),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f48,plain,(
% 2.80/0.97    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,X0,X2)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k2_relset_1(sK3,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) & ~v1_xboole_0(sK3))) )),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f47,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK2,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f50,plain,(
% 2.80/0.97    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,sK2,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f49,f48,f47])).
% 2.80/0.97  
% 2.80/0.97  fof(f73,plain,(
% 2.80/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 2.80/0.97    inference(cnf_transformation,[],[f50])).
% 2.80/0.97  
% 2.80/0.97  fof(f8,axiom,(
% 2.80/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f20,plain,(
% 2.80/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.80/0.97    inference(unused_predicate_definition_removal,[],[f8])).
% 2.80/0.97  
% 2.80/0.97  fof(f25,plain,(
% 2.80/0.97    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.80/0.97    inference(ennf_transformation,[],[f20])).
% 2.80/0.97  
% 2.80/0.97  fof(f59,plain,(
% 2.80/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f25])).
% 2.80/0.97  
% 2.80/0.97  fof(f17,axiom,(
% 2.80/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f35,plain,(
% 2.80/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.80/0.97    inference(ennf_transformation,[],[f17])).
% 2.80/0.97  
% 2.80/0.97  fof(f36,plain,(
% 2.80/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.80/0.97    inference(flattening,[],[f35])).
% 2.80/0.97  
% 2.80/0.97  fof(f70,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f36])).
% 2.80/0.97  
% 2.80/0.97  fof(f9,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f26,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.80/0.97    inference(ennf_transformation,[],[f9])).
% 2.80/0.97  
% 2.80/0.97  fof(f60,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f26])).
% 2.80/0.97  
% 2.80/0.97  fof(f15,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f33,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.97    inference(ennf_transformation,[],[f15])).
% 2.80/0.97  
% 2.80/0.97  fof(f68,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f33])).
% 2.80/0.97  
% 2.80/0.97  fof(f75,plain,(
% 2.80/0.97    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,sK2,sK4)) | ~m1_subset_1(X3,sK3)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f50])).
% 2.80/0.97  
% 2.80/0.97  fof(f14,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f21,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.80/0.97    inference(pure_predicate_removal,[],[f14])).
% 2.80/0.97  
% 2.80/0.97  fof(f32,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.97    inference(ennf_transformation,[],[f21])).
% 2.80/0.97  
% 2.80/0.97  fof(f67,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f32])).
% 2.80/0.97  
% 2.80/0.97  fof(f11,axiom,(
% 2.80/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f28,plain,(
% 2.80/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.80/0.97    inference(ennf_transformation,[],[f11])).
% 2.80/0.97  
% 2.80/0.97  fof(f29,plain,(
% 2.80/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.80/0.97    inference(flattening,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f62,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f29])).
% 2.80/0.97  
% 2.80/0.97  fof(f13,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f31,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.97    inference(ennf_transformation,[],[f13])).
% 2.80/0.97  
% 2.80/0.97  fof(f66,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f31])).
% 2.80/0.97  
% 2.80/0.97  fof(f12,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f30,plain,(
% 2.80/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 2.80/0.97    inference(ennf_transformation,[],[f12])).
% 2.80/0.97  
% 2.80/0.97  fof(f45,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.80/0.97    inference(nnf_transformation,[],[f30])).
% 2.80/0.97  
% 2.80/0.97  fof(f46,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.80/0.97    inference(flattening,[],[f45])).
% 2.80/0.97  
% 2.80/0.97  fof(f63,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f46])).
% 2.80/0.97  
% 2.80/0.97  fof(f7,axiom,(
% 2.80/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f24,plain,(
% 2.80/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.80/0.97    inference(ennf_transformation,[],[f7])).
% 2.80/0.97  
% 2.80/0.97  fof(f58,plain,(
% 2.80/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f24])).
% 2.80/0.97  
% 2.80/0.97  fof(f10,axiom,(
% 2.80/0.97    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f27,plain,(
% 2.80/0.97    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f10])).
% 2.80/0.97  
% 2.80/0.97  fof(f61,plain,(
% 2.80/0.97    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f27])).
% 2.80/0.97  
% 2.80/0.97  fof(f2,axiom,(
% 2.80/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f22,plain,(
% 2.80/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f2])).
% 2.80/0.97  
% 2.80/0.97  fof(f53,plain,(
% 2.80/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f22])).
% 2.80/0.97  
% 2.80/0.97  fof(f16,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f34,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.97    inference(ennf_transformation,[],[f16])).
% 2.80/0.97  
% 2.80/0.97  fof(f69,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f34])).
% 2.80/0.97  
% 2.80/0.97  fof(f74,plain,(
% 2.80/0.97    k1_xboole_0 != k2_relset_1(sK3,sK2,sK4)),
% 2.80/0.97    inference(cnf_transformation,[],[f50])).
% 2.80/0.97  
% 2.80/0.97  cnf(c_0,plain,
% 2.80/0.97      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.80/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_951,plain,
% 2.80/0.97      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.80/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4,plain,
% 2.80/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_947,plain,
% 2.80/0.97      ( v1_xboole_0(X0) != iProver_top
% 2.80/0.97      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_6,plain,
% 2.80/0.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_946,plain,
% 2.80/0.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_5,plain,
% 2.80/0.97      ( k2_subset_1(X0) = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_962,plain,
% 2.80/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.80/0.97      inference(light_normalisation,[status(thm)],[c_946,c_5]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_22,negated_conjecture,
% 2.80/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 2.80/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_935,plain,
% 2.80/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_8,plain,
% 2.80/0.97      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_19,plain,
% 2.80/0.97      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.80/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
% 2.80/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_260,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.80/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
% 2.80/0.97      | X5 != X1
% 2.80/0.97      | k1_relat_1(X2) != X0 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_261,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.80/0.97      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X3)) ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_260]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_932,plain,
% 2.80/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 2.80/0.97      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X3)) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1988,plain,
% 2.80/0.97      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
% 2.80/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_935,c_932]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_9,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.97      | ~ r2_hidden(X2,X0)
% 2.80/0.97      | ~ v1_xboole_0(X1) ),
% 2.80/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_944,plain,
% 2.80/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.80/0.97      | r2_hidden(X2,X0) != iProver_top
% 2.80/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3033,plain,
% 2.80/0.97      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top
% 2.80/0.97      | r2_hidden(X1,sK4) != iProver_top
% 2.80/0.97      | v1_xboole_0(k2_zfmisc_1(X0,sK2)) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1988,c_944]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3804,plain,
% 2.80/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.80/0.97      | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_962,c_3033]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4582,plain,
% 2.80/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.80/0.97      | v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_947,c_3804]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_17,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.80/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_938,plain,
% 2.80/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.80/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2971,plain,
% 2.80/0.97      ( k1_relset_1(sK3,sK2,sK4) = k1_relat_1(sK4) ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_935,c_938]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_20,negated_conjecture,
% 2.80/0.97      ( ~ m1_subset_1(X0,sK3)
% 2.80/0.97      | ~ r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_936,plain,
% 2.80/0.97      ( m1_subset_1(X0,sK3) != iProver_top
% 2.80/0.97      | r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1437,plain,
% 2.80/0.97      ( m1_subset_1(sK0(k1_relset_1(sK3,sK2,sK4)),sK3) != iProver_top
% 2.80/0.97      | v1_xboole_0(k1_relset_1(sK3,sK2,sK4)) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_951,c_936]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3369,plain,
% 2.80/0.97      ( m1_subset_1(sK0(k1_relat_1(sK4)),sK3) != iProver_top
% 2.80/0.97      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 2.80/0.97      inference(demodulation,[status(thm)],[c_2971,c_1437]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_16,plain,
% 2.80/0.97      ( v4_relat_1(X0,X1)
% 2.80/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.80/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_11,plain,
% 2.80/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_277,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | ~ v1_relat_1(X0)
% 2.80/0.97      | k7_relat_1(X0,X1) = X0 ),
% 2.80/0.97      inference(resolution,[status(thm)],[c_16,c_11]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_15,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | v1_relat_1(X0) ),
% 2.80/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_281,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | k7_relat_1(X0,X1) = X0 ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_277,c_16,c_15,c_11]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_931,plain,
% 2.80/0.97      ( k7_relat_1(X0,X1) = X0
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1297,plain,
% 2.80/0.97      ( k7_relat_1(sK4,sK3) = sK4 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_935,c_931]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_14,plain,
% 2.80/0.97      ( r2_hidden(X0,X1)
% 2.80/0.97      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 2.80/0.97      | ~ v1_relat_1(X2) ),
% 2.80/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_940,plain,
% 2.80/0.97      ( r2_hidden(X0,X1) = iProver_top
% 2.80/0.97      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 2.80/0.97      | v1_relat_1(X2) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3053,plain,
% 2.80/0.97      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.80/0.97      | r2_hidden(X0,sK3) = iProver_top
% 2.80/0.97      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1297,c_940]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_27,plain,
% 2.80/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1124,plain,
% 2.80/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.80/0.97      | v1_relat_1(sK4) ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1125,plain,
% 2.80/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.80/0.97      | v1_relat_1(sK4) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_1124]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3681,plain,
% 2.80/0.97      ( r2_hidden(X0,sK3) = iProver_top
% 2.80/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_3053,c_27,c_1125]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3682,plain,
% 2.80/0.97      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.80/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 2.80/0.97      inference(renaming,[status(thm)],[c_3681]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3689,plain,
% 2.80/0.97      ( r2_hidden(sK0(k1_relat_1(sK4)),sK3) = iProver_top
% 2.80/0.97      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_951,c_3682]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_7,plain,
% 2.80/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.80/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_945,plain,
% 2.80/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 2.80/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4590,plain,
% 2.80/0.97      ( m1_subset_1(sK0(k1_relat_1(sK4)),sK3) = iProver_top
% 2.80/0.97      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_3689,c_945]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4698,plain,
% 2.80/0.97      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_4582,c_3369,c_4590]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4705,plain,
% 2.80/0.97      ( v1_xboole_0(sK4) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_951,c_4698]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_10,plain,
% 2.80/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_943,plain,
% 2.80/0.97      ( v1_xboole_0(X0) != iProver_top
% 2.80/0.97      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2,plain,
% 2.80/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_949,plain,
% 2.80/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1432,plain,
% 2.80/0.97      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_943,c_949]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4913,plain,
% 2.80/0.97      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_4705,c_1432]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_18,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.80/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_937,plain,
% 2.80/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.80/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2290,plain,
% 2.80/0.97      ( k2_relset_1(sK3,sK2,sK4) = k2_relat_1(sK4) ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_935,c_937]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_21,negated_conjecture,
% 2.80/0.97      ( k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
% 2.80/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2595,plain,
% 2.80/0.97      ( k2_relat_1(sK4) != k1_xboole_0 ),
% 2.80/0.97      inference(demodulation,[status(thm)],[c_2290,c_21]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(contradiction,plain,
% 2.80/0.97      ( $false ),
% 2.80/0.97      inference(minisat,[status(thm)],[c_4913,c_2595]) ).
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  ------                               Statistics
% 2.80/0.97  
% 2.80/0.97  ------ General
% 2.80/0.97  
% 2.80/0.97  abstr_ref_over_cycles:                  0
% 2.80/0.97  abstr_ref_under_cycles:                 0
% 2.80/0.97  gc_basic_clause_elim:                   0
% 2.80/0.97  forced_gc_time:                         0
% 2.80/0.97  parsing_time:                           0.008
% 2.80/0.97  unif_index_cands_time:                  0.
% 2.80/0.97  unif_index_add_time:                    0.
% 2.80/0.97  orderings_time:                         0.
% 2.80/0.97  out_proof_time:                         0.008
% 2.80/0.97  total_time:                             0.158
% 2.80/0.97  num_of_symbols:                         51
% 2.80/0.97  num_of_terms:                           4803
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing
% 2.80/0.97  
% 2.80/0.97  num_of_splits:                          0
% 2.80/0.97  num_of_split_atoms:                     0
% 2.80/0.97  num_of_reused_defs:                     0
% 2.80/0.97  num_eq_ax_congr_red:                    21
% 2.80/0.97  num_of_sem_filtered_clauses:            1
% 2.80/0.97  num_of_subtypes:                        0
% 2.80/0.97  monotx_restored_types:                  0
% 2.80/0.97  sat_num_of_epr_types:                   0
% 2.80/0.97  sat_num_of_non_cyclic_types:            0
% 2.80/0.97  sat_guarded_non_collapsed_types:        0
% 2.80/0.97  num_pure_diseq_elim:                    0
% 2.80/0.97  simp_replaced_by:                       0
% 2.80/0.97  res_preprocessed:                       115
% 2.80/0.97  prep_upred:                             0
% 2.80/0.97  prep_unflattend:                        8
% 2.80/0.97  smt_new_axioms:                         0
% 2.80/0.97  pred_elim_cands:                        4
% 2.80/0.97  pred_elim:                              2
% 2.80/0.97  pred_elim_cl:                           2
% 2.80/0.97  pred_elim_cycles:                       4
% 2.80/0.97  merged_defs:                            0
% 2.80/0.97  merged_defs_ncl:                        0
% 2.80/0.97  bin_hyper_res:                          0
% 2.80/0.97  prep_cycles:                            4
% 2.80/0.97  pred_elim_time:                         0.003
% 2.80/0.97  splitting_time:                         0.
% 2.80/0.97  sem_filter_time:                        0.
% 2.80/0.97  monotx_time:                            0.
% 2.80/0.97  subtype_inf_time:                       0.
% 2.80/0.97  
% 2.80/0.97  ------ Problem properties
% 2.80/0.97  
% 2.80/0.97  clauses:                                23
% 2.80/0.97  conjectures:                            5
% 2.80/0.97  epr:                                    6
% 2.80/0.97  horn:                                   22
% 2.80/0.97  ground:                                 5
% 2.80/0.97  unary:                                  7
% 2.80/0.97  binary:                                 11
% 2.80/0.97  lits:                                   45
% 2.80/0.97  lits_eq:                                6
% 2.80/0.97  fd_pure:                                0
% 2.80/0.97  fd_pseudo:                              0
% 2.80/0.97  fd_cond:                                1
% 2.80/0.97  fd_pseudo_cond:                         0
% 2.80/0.97  ac_symbols:                             0
% 2.80/0.97  
% 2.80/0.97  ------ Propositional Solver
% 2.80/0.97  
% 2.80/0.97  prop_solver_calls:                      27
% 2.80/0.97  prop_fast_solver_calls:                 622
% 2.80/0.97  smt_solver_calls:                       0
% 2.80/0.97  smt_fast_solver_calls:                  0
% 2.80/0.97  prop_num_of_clauses:                    2211
% 2.80/0.97  prop_preprocess_simplified:             7028
% 2.80/0.97  prop_fo_subsumed:                       4
% 2.80/0.97  prop_solver_time:                       0.
% 2.80/0.97  smt_solver_time:                        0.
% 2.80/0.97  smt_fast_solver_time:                   0.
% 2.80/0.97  prop_fast_solver_time:                  0.
% 2.80/0.97  prop_unsat_core_time:                   0.
% 2.80/0.97  
% 2.80/0.97  ------ QBF
% 2.80/0.97  
% 2.80/0.97  qbf_q_res:                              0
% 2.80/0.97  qbf_num_tautologies:                    0
% 2.80/0.97  qbf_prep_cycles:                        0
% 2.80/0.97  
% 2.80/0.97  ------ BMC1
% 2.80/0.97  
% 2.80/0.97  bmc1_current_bound:                     -1
% 2.80/0.97  bmc1_last_solved_bound:                 -1
% 2.80/0.97  bmc1_unsat_core_size:                   -1
% 2.80/0.97  bmc1_unsat_core_parents_size:           -1
% 2.80/0.97  bmc1_merge_next_fun:                    0
% 2.80/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation
% 2.80/0.97  
% 2.80/0.97  inst_num_of_clauses:                    673
% 2.80/0.97  inst_num_in_passive:                    360
% 2.80/0.97  inst_num_in_active:                     262
% 2.80/0.97  inst_num_in_unprocessed:                51
% 2.80/0.97  inst_num_of_loops:                      280
% 2.80/0.97  inst_num_of_learning_restarts:          0
% 2.80/0.97  inst_num_moves_active_passive:          17
% 2.80/0.97  inst_lit_activity:                      0
% 2.80/0.97  inst_lit_activity_moves:                0
% 2.80/0.97  inst_num_tautologies:                   0
% 2.80/0.97  inst_num_prop_implied:                  0
% 2.80/0.97  inst_num_existing_simplified:           0
% 2.80/0.97  inst_num_eq_res_simplified:             0
% 2.80/0.97  inst_num_child_elim:                    0
% 2.80/0.97  inst_num_of_dismatching_blockings:      86
% 2.80/0.97  inst_num_of_non_proper_insts:           374
% 2.80/0.97  inst_num_of_duplicates:                 0
% 2.80/0.97  inst_inst_num_from_inst_to_res:         0
% 2.80/0.97  inst_dismatching_checking_time:         0.
% 2.80/0.97  
% 2.80/0.97  ------ Resolution
% 2.80/0.97  
% 2.80/0.97  res_num_of_clauses:                     0
% 2.80/0.97  res_num_in_passive:                     0
% 2.80/0.97  res_num_in_active:                      0
% 2.80/0.97  res_num_of_loops:                       119
% 2.80/0.97  res_forward_subset_subsumed:            28
% 2.80/0.97  res_backward_subset_subsumed:           0
% 2.80/0.97  res_forward_subsumed:                   0
% 2.80/0.97  res_backward_subsumed:                  0
% 2.80/0.97  res_forward_subsumption_resolution:     0
% 2.80/0.97  res_backward_subsumption_resolution:    0
% 2.80/0.97  res_clause_to_clause_subsumption:       179
% 2.80/0.97  res_orphan_elimination:                 0
% 2.80/0.97  res_tautology_del:                      48
% 2.80/0.97  res_num_eq_res_simplified:              0
% 2.80/0.97  res_num_sel_changes:                    0
% 2.80/0.97  res_moves_from_active_to_pass:          0
% 2.80/0.97  
% 2.80/0.97  ------ Superposition
% 2.80/0.97  
% 2.80/0.97  sup_time_total:                         0.
% 2.80/0.97  sup_time_generating:                    0.
% 2.80/0.97  sup_time_sim_full:                      0.
% 2.80/0.97  sup_time_sim_immed:                     0.
% 2.80/0.97  
% 2.80/0.97  sup_num_of_clauses:                     60
% 2.80/0.97  sup_num_in_active:                      34
% 2.80/0.97  sup_num_in_passive:                     26
% 2.80/0.97  sup_num_of_loops:                       55
% 2.80/0.97  sup_fw_superposition:                   45
% 2.80/0.97  sup_bw_superposition:                   30
% 2.80/0.97  sup_immediate_simplified:               11
% 2.80/0.97  sup_given_eliminated:                   2
% 2.80/0.97  comparisons_done:                       0
% 2.80/0.97  comparisons_avoided:                    0
% 2.80/0.97  
% 2.80/0.97  ------ Simplifications
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  sim_fw_subset_subsumed:                 6
% 2.80/0.97  sim_bw_subset_subsumed:                 2
% 2.80/0.97  sim_fw_subsumed:                        3
% 2.80/0.97  sim_bw_subsumed:                        0
% 2.80/0.97  sim_fw_subsumption_res:                 0
% 2.80/0.97  sim_bw_subsumption_res:                 0
% 2.80/0.97  sim_tautology_del:                      10
% 2.80/0.97  sim_eq_tautology_del:                   4
% 2.80/0.97  sim_eq_res_simp:                        0
% 2.80/0.97  sim_fw_demodulated:                     0
% 2.80/0.97  sim_bw_demodulated:                     21
% 2.80/0.97  sim_light_normalised:                   6
% 2.80/0.97  sim_joinable_taut:                      0
% 2.80/0.97  sim_joinable_simp:                      0
% 2.80/0.97  sim_ac_normalised:                      0
% 2.80/0.97  sim_smt_subsumption:                    0
% 2.80/0.97  
%------------------------------------------------------------------------------
