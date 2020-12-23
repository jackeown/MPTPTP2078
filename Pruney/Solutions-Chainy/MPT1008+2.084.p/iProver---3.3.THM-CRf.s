%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:21 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 381 expanded)
%              Number of clauses        :   61 (  75 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  387 (1015 expanded)
%              Number of equality atoms :  221 ( 578 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f38])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f74])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f43,f74,f74,f74,f75,f75,f75,f43])).

fof(f73,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f73,f75,f75])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f75,f75])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_tarski(X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f43,f75])).

fof(f96,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f72,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2839,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2841,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4419,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2839,c_2841])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2842,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4619,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4419,c_2842])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4769,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4619,c_33])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4774,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4769,c_2847])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2852,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5262,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4774,c_2852])).

cnf(c_26,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_383,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_384,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_385,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_387,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3032,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3033,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3032])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3050,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2239,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3035,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_3276,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_5351,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5262,c_28,c_33,c_26,c_387,c_3033,c_3050,c_3276])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2845,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5369,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5351,c_2845])).

cnf(c_5531,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5369,c_33,c_3033])).

cnf(c_5,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2856,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2849,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3950,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2856,c_2849])).

cnf(c_2840,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4298,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2839,c_2840])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK0,sK0,sK0,sK0) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_30,c_28,c_27])).

cnf(c_2838,plain,
    ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2844,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3293,plain,
    ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
    | r1_tarski(k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_funct_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_2844])).

cnf(c_4561,plain,
    ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4298,c_3293])).

cnf(c_4682,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3950,c_4561])).

cnf(c_5538,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5531,c_4682])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5570,plain,
    ( r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5538,c_15])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2861,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5901,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5570,c_2861])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.01  
% 2.46/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/1.01  
% 2.46/1.01  ------  iProver source info
% 2.46/1.01  
% 2.46/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.46/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/1.01  git: non_committed_changes: false
% 2.46/1.01  git: last_make_outside_of_git: false
% 2.46/1.01  
% 2.46/1.01  ------ 
% 2.46/1.01  
% 2.46/1.01  ------ Input Options
% 2.46/1.01  
% 2.46/1.01  --out_options                           all
% 2.46/1.01  --tptp_safe_out                         true
% 2.46/1.01  --problem_path                          ""
% 2.46/1.01  --include_path                          ""
% 2.46/1.01  --clausifier                            res/vclausify_rel
% 2.46/1.01  --clausifier_options                    --mode clausify
% 2.46/1.01  --stdin                                 false
% 2.46/1.01  --stats_out                             all
% 2.46/1.01  
% 2.46/1.01  ------ General Options
% 2.46/1.01  
% 2.46/1.01  --fof                                   false
% 2.46/1.01  --time_out_real                         305.
% 2.46/1.01  --time_out_virtual                      -1.
% 2.46/1.01  --symbol_type_check                     false
% 2.46/1.01  --clausify_out                          false
% 2.46/1.01  --sig_cnt_out                           false
% 2.46/1.01  --trig_cnt_out                          false
% 2.46/1.01  --trig_cnt_out_tolerance                1.
% 2.46/1.01  --trig_cnt_out_sk_spl                   false
% 2.46/1.01  --abstr_cl_out                          false
% 2.46/1.01  
% 2.46/1.01  ------ Global Options
% 2.46/1.01  
% 2.46/1.01  --schedule                              default
% 2.46/1.01  --add_important_lit                     false
% 2.46/1.01  --prop_solver_per_cl                    1000
% 2.46/1.01  --min_unsat_core                        false
% 2.46/1.01  --soft_assumptions                      false
% 2.46/1.01  --soft_lemma_size                       3
% 2.46/1.01  --prop_impl_unit_size                   0
% 2.46/1.01  --prop_impl_unit                        []
% 2.46/1.01  --share_sel_clauses                     true
% 2.46/1.01  --reset_solvers                         false
% 2.46/1.01  --bc_imp_inh                            [conj_cone]
% 2.46/1.01  --conj_cone_tolerance                   3.
% 2.46/1.01  --extra_neg_conj                        none
% 2.46/1.01  --large_theory_mode                     true
% 2.46/1.01  --prolific_symb_bound                   200
% 2.46/1.01  --lt_threshold                          2000
% 2.46/1.01  --clause_weak_htbl                      true
% 2.46/1.01  --gc_record_bc_elim                     false
% 2.46/1.01  
% 2.46/1.01  ------ Preprocessing Options
% 2.46/1.01  
% 2.46/1.01  --preprocessing_flag                    true
% 2.46/1.01  --time_out_prep_mult                    0.1
% 2.46/1.01  --splitting_mode                        input
% 2.46/1.01  --splitting_grd                         true
% 2.46/1.01  --splitting_cvd                         false
% 2.46/1.01  --splitting_cvd_svl                     false
% 2.46/1.01  --splitting_nvd                         32
% 2.46/1.01  --sub_typing                            true
% 2.46/1.01  --prep_gs_sim                           true
% 2.46/1.01  --prep_unflatten                        true
% 2.46/1.01  --prep_res_sim                          true
% 2.46/1.01  --prep_upred                            true
% 2.46/1.01  --prep_sem_filter                       exhaustive
% 2.46/1.01  --prep_sem_filter_out                   false
% 2.46/1.01  --pred_elim                             true
% 2.46/1.01  --res_sim_input                         true
% 2.46/1.01  --eq_ax_congr_red                       true
% 2.46/1.01  --pure_diseq_elim                       true
% 2.46/1.01  --brand_transform                       false
% 2.46/1.01  --non_eq_to_eq                          false
% 2.46/1.01  --prep_def_merge                        true
% 2.46/1.01  --prep_def_merge_prop_impl              false
% 2.46/1.01  --prep_def_merge_mbd                    true
% 2.46/1.01  --prep_def_merge_tr_red                 false
% 2.46/1.01  --prep_def_merge_tr_cl                  false
% 2.46/1.01  --smt_preprocessing                     true
% 2.46/1.01  --smt_ac_axioms                         fast
% 2.46/1.01  --preprocessed_out                      false
% 2.46/1.01  --preprocessed_stats                    false
% 2.46/1.01  
% 2.46/1.01  ------ Abstraction refinement Options
% 2.46/1.01  
% 2.46/1.01  --abstr_ref                             []
% 2.46/1.01  --abstr_ref_prep                        false
% 2.46/1.01  --abstr_ref_until_sat                   false
% 2.46/1.01  --abstr_ref_sig_restrict                funpre
% 2.46/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.01  --abstr_ref_under                       []
% 2.46/1.01  
% 2.46/1.01  ------ SAT Options
% 2.46/1.01  
% 2.46/1.01  --sat_mode                              false
% 2.46/1.01  --sat_fm_restart_options                ""
% 2.46/1.01  --sat_gr_def                            false
% 2.46/1.01  --sat_epr_types                         true
% 2.46/1.01  --sat_non_cyclic_types                  false
% 2.46/1.01  --sat_finite_models                     false
% 2.46/1.01  --sat_fm_lemmas                         false
% 2.46/1.01  --sat_fm_prep                           false
% 2.46/1.02  --sat_fm_uc_incr                        true
% 2.46/1.02  --sat_out_model                         small
% 2.46/1.02  --sat_out_clauses                       false
% 2.46/1.02  
% 2.46/1.02  ------ QBF Options
% 2.46/1.02  
% 2.46/1.02  --qbf_mode                              false
% 2.46/1.02  --qbf_elim_univ                         false
% 2.46/1.02  --qbf_dom_inst                          none
% 2.46/1.02  --qbf_dom_pre_inst                      false
% 2.46/1.02  --qbf_sk_in                             false
% 2.46/1.02  --qbf_pred_elim                         true
% 2.46/1.02  --qbf_split                             512
% 2.46/1.02  
% 2.46/1.02  ------ BMC1 Options
% 2.46/1.02  
% 2.46/1.02  --bmc1_incremental                      false
% 2.46/1.02  --bmc1_axioms                           reachable_all
% 2.46/1.02  --bmc1_min_bound                        0
% 2.46/1.02  --bmc1_max_bound                        -1
% 2.46/1.02  --bmc1_max_bound_default                -1
% 2.46/1.02  --bmc1_symbol_reachability              true
% 2.46/1.02  --bmc1_property_lemmas                  false
% 2.46/1.02  --bmc1_k_induction                      false
% 2.46/1.02  --bmc1_non_equiv_states                 false
% 2.46/1.02  --bmc1_deadlock                         false
% 2.46/1.02  --bmc1_ucm                              false
% 2.46/1.02  --bmc1_add_unsat_core                   none
% 2.46/1.02  --bmc1_unsat_core_children              false
% 2.46/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.02  --bmc1_out_stat                         full
% 2.46/1.02  --bmc1_ground_init                      false
% 2.46/1.02  --bmc1_pre_inst_next_state              false
% 2.46/1.02  --bmc1_pre_inst_state                   false
% 2.46/1.02  --bmc1_pre_inst_reach_state             false
% 2.46/1.02  --bmc1_out_unsat_core                   false
% 2.46/1.02  --bmc1_aig_witness_out                  false
% 2.46/1.02  --bmc1_verbose                          false
% 2.46/1.02  --bmc1_dump_clauses_tptp                false
% 2.46/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.02  --bmc1_dump_file                        -
% 2.46/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.02  --bmc1_ucm_extend_mode                  1
% 2.46/1.02  --bmc1_ucm_init_mode                    2
% 2.46/1.02  --bmc1_ucm_cone_mode                    none
% 2.46/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.02  --bmc1_ucm_relax_model                  4
% 2.46/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.02  --bmc1_ucm_layered_model                none
% 2.46/1.02  --bmc1_ucm_max_lemma_size               10
% 2.46/1.02  
% 2.46/1.02  ------ AIG Options
% 2.46/1.02  
% 2.46/1.02  --aig_mode                              false
% 2.46/1.02  
% 2.46/1.02  ------ Instantiation Options
% 2.46/1.02  
% 2.46/1.02  --instantiation_flag                    true
% 2.46/1.02  --inst_sos_flag                         false
% 2.46/1.02  --inst_sos_phase                        true
% 2.46/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.02  --inst_lit_sel_side                     num_symb
% 2.46/1.02  --inst_solver_per_active                1400
% 2.46/1.02  --inst_solver_calls_frac                1.
% 2.46/1.02  --inst_passive_queue_type               priority_queues
% 2.46/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.02  --inst_passive_queues_freq              [25;2]
% 2.46/1.02  --inst_dismatching                      true
% 2.46/1.02  --inst_eager_unprocessed_to_passive     true
% 2.46/1.02  --inst_prop_sim_given                   true
% 2.46/1.02  --inst_prop_sim_new                     false
% 2.46/1.02  --inst_subs_new                         false
% 2.46/1.02  --inst_eq_res_simp                      false
% 2.46/1.02  --inst_subs_given                       false
% 2.46/1.02  --inst_orphan_elimination               true
% 2.46/1.02  --inst_learning_loop_flag               true
% 2.46/1.02  --inst_learning_start                   3000
% 2.46/1.02  --inst_learning_factor                  2
% 2.46/1.02  --inst_start_prop_sim_after_learn       3
% 2.46/1.02  --inst_sel_renew                        solver
% 2.46/1.02  --inst_lit_activity_flag                true
% 2.46/1.02  --inst_restr_to_given                   false
% 2.46/1.02  --inst_activity_threshold               500
% 2.46/1.02  --inst_out_proof                        true
% 2.46/1.02  
% 2.46/1.02  ------ Resolution Options
% 2.46/1.02  
% 2.46/1.02  --resolution_flag                       true
% 2.46/1.02  --res_lit_sel                           adaptive
% 2.46/1.02  --res_lit_sel_side                      none
% 2.46/1.02  --res_ordering                          kbo
% 2.46/1.02  --res_to_prop_solver                    active
% 2.46/1.02  --res_prop_simpl_new                    false
% 2.46/1.02  --res_prop_simpl_given                  true
% 2.46/1.02  --res_passive_queue_type                priority_queues
% 2.46/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.02  --res_passive_queues_freq               [15;5]
% 2.46/1.02  --res_forward_subs                      full
% 2.46/1.02  --res_backward_subs                     full
% 2.46/1.02  --res_forward_subs_resolution           true
% 2.46/1.02  --res_backward_subs_resolution          true
% 2.46/1.02  --res_orphan_elimination                true
% 2.46/1.02  --res_time_limit                        2.
% 2.46/1.02  --res_out_proof                         true
% 2.46/1.02  
% 2.46/1.02  ------ Superposition Options
% 2.46/1.02  
% 2.46/1.02  --superposition_flag                    true
% 2.46/1.02  --sup_passive_queue_type                priority_queues
% 2.46/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.02  --demod_completeness_check              fast
% 2.46/1.02  --demod_use_ground                      true
% 2.46/1.02  --sup_to_prop_solver                    passive
% 2.46/1.02  --sup_prop_simpl_new                    true
% 2.46/1.02  --sup_prop_simpl_given                  true
% 2.46/1.02  --sup_fun_splitting                     false
% 2.46/1.02  --sup_smt_interval                      50000
% 2.46/1.02  
% 2.46/1.02  ------ Superposition Simplification Setup
% 2.46/1.02  
% 2.46/1.02  --sup_indices_passive                   []
% 2.46/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_full_bw                           [BwDemod]
% 2.46/1.02  --sup_immed_triv                        [TrivRules]
% 2.46/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_immed_bw_main                     []
% 2.46/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.02  
% 2.46/1.02  ------ Combination Options
% 2.46/1.02  
% 2.46/1.02  --comb_res_mult                         3
% 2.46/1.02  --comb_sup_mult                         2
% 2.46/1.02  --comb_inst_mult                        10
% 2.46/1.02  
% 2.46/1.02  ------ Debug Options
% 2.46/1.02  
% 2.46/1.02  --dbg_backtrace                         false
% 2.46/1.02  --dbg_dump_prop_clauses                 false
% 2.46/1.02  --dbg_dump_prop_clauses_file            -
% 2.46/1.02  --dbg_out_stat                          false
% 2.46/1.02  ------ Parsing...
% 2.46/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/1.02  
% 2.46/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.46/1.02  
% 2.46/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/1.02  
% 2.46/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/1.02  ------ Proving...
% 2.46/1.02  ------ Problem Properties 
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  clauses                                 29
% 2.46/1.02  conjectures                             3
% 2.46/1.02  EPR                                     3
% 2.46/1.02  Horn                                    28
% 2.46/1.02  unary                                   14
% 2.46/1.02  binary                                  10
% 2.46/1.02  lits                                    55
% 2.46/1.02  lits eq                                 20
% 2.46/1.02  fd_pure                                 0
% 2.46/1.02  fd_pseudo                               0
% 2.46/1.02  fd_cond                                 2
% 2.46/1.02  fd_pseudo_cond                          1
% 2.46/1.02  AC symbols                              0
% 2.46/1.02  
% 2.46/1.02  ------ Schedule dynamic 5 is on 
% 2.46/1.02  
% 2.46/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  ------ 
% 2.46/1.02  Current options:
% 2.46/1.02  ------ 
% 2.46/1.02  
% 2.46/1.02  ------ Input Options
% 2.46/1.02  
% 2.46/1.02  --out_options                           all
% 2.46/1.02  --tptp_safe_out                         true
% 2.46/1.02  --problem_path                          ""
% 2.46/1.02  --include_path                          ""
% 2.46/1.02  --clausifier                            res/vclausify_rel
% 2.46/1.02  --clausifier_options                    --mode clausify
% 2.46/1.02  --stdin                                 false
% 2.46/1.02  --stats_out                             all
% 2.46/1.02  
% 2.46/1.02  ------ General Options
% 2.46/1.02  
% 2.46/1.02  --fof                                   false
% 2.46/1.02  --time_out_real                         305.
% 2.46/1.02  --time_out_virtual                      -1.
% 2.46/1.02  --symbol_type_check                     false
% 2.46/1.02  --clausify_out                          false
% 2.46/1.02  --sig_cnt_out                           false
% 2.46/1.02  --trig_cnt_out                          false
% 2.46/1.02  --trig_cnt_out_tolerance                1.
% 2.46/1.02  --trig_cnt_out_sk_spl                   false
% 2.46/1.02  --abstr_cl_out                          false
% 2.46/1.02  
% 2.46/1.02  ------ Global Options
% 2.46/1.02  
% 2.46/1.02  --schedule                              default
% 2.46/1.02  --add_important_lit                     false
% 2.46/1.02  --prop_solver_per_cl                    1000
% 2.46/1.02  --min_unsat_core                        false
% 2.46/1.02  --soft_assumptions                      false
% 2.46/1.02  --soft_lemma_size                       3
% 2.46/1.02  --prop_impl_unit_size                   0
% 2.46/1.02  --prop_impl_unit                        []
% 2.46/1.02  --share_sel_clauses                     true
% 2.46/1.02  --reset_solvers                         false
% 2.46/1.02  --bc_imp_inh                            [conj_cone]
% 2.46/1.02  --conj_cone_tolerance                   3.
% 2.46/1.02  --extra_neg_conj                        none
% 2.46/1.02  --large_theory_mode                     true
% 2.46/1.02  --prolific_symb_bound                   200
% 2.46/1.02  --lt_threshold                          2000
% 2.46/1.02  --clause_weak_htbl                      true
% 2.46/1.02  --gc_record_bc_elim                     false
% 2.46/1.02  
% 2.46/1.02  ------ Preprocessing Options
% 2.46/1.02  
% 2.46/1.02  --preprocessing_flag                    true
% 2.46/1.02  --time_out_prep_mult                    0.1
% 2.46/1.02  --splitting_mode                        input
% 2.46/1.02  --splitting_grd                         true
% 2.46/1.02  --splitting_cvd                         false
% 2.46/1.02  --splitting_cvd_svl                     false
% 2.46/1.02  --splitting_nvd                         32
% 2.46/1.02  --sub_typing                            true
% 2.46/1.02  --prep_gs_sim                           true
% 2.46/1.02  --prep_unflatten                        true
% 2.46/1.02  --prep_res_sim                          true
% 2.46/1.02  --prep_upred                            true
% 2.46/1.02  --prep_sem_filter                       exhaustive
% 2.46/1.02  --prep_sem_filter_out                   false
% 2.46/1.02  --pred_elim                             true
% 2.46/1.02  --res_sim_input                         true
% 2.46/1.02  --eq_ax_congr_red                       true
% 2.46/1.02  --pure_diseq_elim                       true
% 2.46/1.02  --brand_transform                       false
% 2.46/1.02  --non_eq_to_eq                          false
% 2.46/1.02  --prep_def_merge                        true
% 2.46/1.02  --prep_def_merge_prop_impl              false
% 2.46/1.02  --prep_def_merge_mbd                    true
% 2.46/1.02  --prep_def_merge_tr_red                 false
% 2.46/1.02  --prep_def_merge_tr_cl                  false
% 2.46/1.02  --smt_preprocessing                     true
% 2.46/1.02  --smt_ac_axioms                         fast
% 2.46/1.02  --preprocessed_out                      false
% 2.46/1.02  --preprocessed_stats                    false
% 2.46/1.02  
% 2.46/1.02  ------ Abstraction refinement Options
% 2.46/1.02  
% 2.46/1.02  --abstr_ref                             []
% 2.46/1.02  --abstr_ref_prep                        false
% 2.46/1.02  --abstr_ref_until_sat                   false
% 2.46/1.02  --abstr_ref_sig_restrict                funpre
% 2.46/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.02  --abstr_ref_under                       []
% 2.46/1.02  
% 2.46/1.02  ------ SAT Options
% 2.46/1.02  
% 2.46/1.02  --sat_mode                              false
% 2.46/1.02  --sat_fm_restart_options                ""
% 2.46/1.02  --sat_gr_def                            false
% 2.46/1.02  --sat_epr_types                         true
% 2.46/1.02  --sat_non_cyclic_types                  false
% 2.46/1.02  --sat_finite_models                     false
% 2.46/1.02  --sat_fm_lemmas                         false
% 2.46/1.02  --sat_fm_prep                           false
% 2.46/1.02  --sat_fm_uc_incr                        true
% 2.46/1.02  --sat_out_model                         small
% 2.46/1.02  --sat_out_clauses                       false
% 2.46/1.02  
% 2.46/1.02  ------ QBF Options
% 2.46/1.02  
% 2.46/1.02  --qbf_mode                              false
% 2.46/1.02  --qbf_elim_univ                         false
% 2.46/1.02  --qbf_dom_inst                          none
% 2.46/1.02  --qbf_dom_pre_inst                      false
% 2.46/1.02  --qbf_sk_in                             false
% 2.46/1.02  --qbf_pred_elim                         true
% 2.46/1.02  --qbf_split                             512
% 2.46/1.02  
% 2.46/1.02  ------ BMC1 Options
% 2.46/1.02  
% 2.46/1.02  --bmc1_incremental                      false
% 2.46/1.02  --bmc1_axioms                           reachable_all
% 2.46/1.02  --bmc1_min_bound                        0
% 2.46/1.02  --bmc1_max_bound                        -1
% 2.46/1.02  --bmc1_max_bound_default                -1
% 2.46/1.02  --bmc1_symbol_reachability              true
% 2.46/1.02  --bmc1_property_lemmas                  false
% 2.46/1.02  --bmc1_k_induction                      false
% 2.46/1.02  --bmc1_non_equiv_states                 false
% 2.46/1.02  --bmc1_deadlock                         false
% 2.46/1.02  --bmc1_ucm                              false
% 2.46/1.02  --bmc1_add_unsat_core                   none
% 2.46/1.02  --bmc1_unsat_core_children              false
% 2.46/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.02  --bmc1_out_stat                         full
% 2.46/1.02  --bmc1_ground_init                      false
% 2.46/1.02  --bmc1_pre_inst_next_state              false
% 2.46/1.02  --bmc1_pre_inst_state                   false
% 2.46/1.02  --bmc1_pre_inst_reach_state             false
% 2.46/1.02  --bmc1_out_unsat_core                   false
% 2.46/1.02  --bmc1_aig_witness_out                  false
% 2.46/1.02  --bmc1_verbose                          false
% 2.46/1.02  --bmc1_dump_clauses_tptp                false
% 2.46/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.02  --bmc1_dump_file                        -
% 2.46/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.02  --bmc1_ucm_extend_mode                  1
% 2.46/1.02  --bmc1_ucm_init_mode                    2
% 2.46/1.02  --bmc1_ucm_cone_mode                    none
% 2.46/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.02  --bmc1_ucm_relax_model                  4
% 2.46/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.02  --bmc1_ucm_layered_model                none
% 2.46/1.02  --bmc1_ucm_max_lemma_size               10
% 2.46/1.02  
% 2.46/1.02  ------ AIG Options
% 2.46/1.02  
% 2.46/1.02  --aig_mode                              false
% 2.46/1.02  
% 2.46/1.02  ------ Instantiation Options
% 2.46/1.02  
% 2.46/1.02  --instantiation_flag                    true
% 2.46/1.02  --inst_sos_flag                         false
% 2.46/1.02  --inst_sos_phase                        true
% 2.46/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.02  --inst_lit_sel_side                     none
% 2.46/1.02  --inst_solver_per_active                1400
% 2.46/1.02  --inst_solver_calls_frac                1.
% 2.46/1.02  --inst_passive_queue_type               priority_queues
% 2.46/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.02  --inst_passive_queues_freq              [25;2]
% 2.46/1.02  --inst_dismatching                      true
% 2.46/1.02  --inst_eager_unprocessed_to_passive     true
% 2.46/1.02  --inst_prop_sim_given                   true
% 2.46/1.02  --inst_prop_sim_new                     false
% 2.46/1.02  --inst_subs_new                         false
% 2.46/1.02  --inst_eq_res_simp                      false
% 2.46/1.02  --inst_subs_given                       false
% 2.46/1.02  --inst_orphan_elimination               true
% 2.46/1.02  --inst_learning_loop_flag               true
% 2.46/1.02  --inst_learning_start                   3000
% 2.46/1.02  --inst_learning_factor                  2
% 2.46/1.02  --inst_start_prop_sim_after_learn       3
% 2.46/1.02  --inst_sel_renew                        solver
% 2.46/1.02  --inst_lit_activity_flag                true
% 2.46/1.02  --inst_restr_to_given                   false
% 2.46/1.02  --inst_activity_threshold               500
% 2.46/1.02  --inst_out_proof                        true
% 2.46/1.02  
% 2.46/1.02  ------ Resolution Options
% 2.46/1.02  
% 2.46/1.02  --resolution_flag                       false
% 2.46/1.02  --res_lit_sel                           adaptive
% 2.46/1.02  --res_lit_sel_side                      none
% 2.46/1.02  --res_ordering                          kbo
% 2.46/1.02  --res_to_prop_solver                    active
% 2.46/1.02  --res_prop_simpl_new                    false
% 2.46/1.02  --res_prop_simpl_given                  true
% 2.46/1.02  --res_passive_queue_type                priority_queues
% 2.46/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.02  --res_passive_queues_freq               [15;5]
% 2.46/1.02  --res_forward_subs                      full
% 2.46/1.02  --res_backward_subs                     full
% 2.46/1.02  --res_forward_subs_resolution           true
% 2.46/1.02  --res_backward_subs_resolution          true
% 2.46/1.02  --res_orphan_elimination                true
% 2.46/1.02  --res_time_limit                        2.
% 2.46/1.02  --res_out_proof                         true
% 2.46/1.02  
% 2.46/1.02  ------ Superposition Options
% 2.46/1.02  
% 2.46/1.02  --superposition_flag                    true
% 2.46/1.02  --sup_passive_queue_type                priority_queues
% 2.46/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.02  --demod_completeness_check              fast
% 2.46/1.02  --demod_use_ground                      true
% 2.46/1.02  --sup_to_prop_solver                    passive
% 2.46/1.02  --sup_prop_simpl_new                    true
% 2.46/1.02  --sup_prop_simpl_given                  true
% 2.46/1.02  --sup_fun_splitting                     false
% 2.46/1.02  --sup_smt_interval                      50000
% 2.46/1.02  
% 2.46/1.02  ------ Superposition Simplification Setup
% 2.46/1.02  
% 2.46/1.02  --sup_indices_passive                   []
% 2.46/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_full_bw                           [BwDemod]
% 2.46/1.02  --sup_immed_triv                        [TrivRules]
% 2.46/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_immed_bw_main                     []
% 2.46/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.02  
% 2.46/1.02  ------ Combination Options
% 2.46/1.02  
% 2.46/1.02  --comb_res_mult                         3
% 2.46/1.02  --comb_sup_mult                         2
% 2.46/1.02  --comb_inst_mult                        10
% 2.46/1.02  
% 2.46/1.02  ------ Debug Options
% 2.46/1.02  
% 2.46/1.02  --dbg_backtrace                         false
% 2.46/1.02  --dbg_dump_prop_clauses                 false
% 2.46/1.02  --dbg_dump_prop_clauses_file            -
% 2.46/1.02  --dbg_out_stat                          false
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  ------ Proving...
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  % SZS status Theorem for theBenchmark.p
% 2.46/1.02  
% 2.46/1.02   Resolution empty clause
% 2.46/1.02  
% 2.46/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/1.02  
% 2.46/1.02  fof(f17,conjecture,(
% 2.46/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f18,negated_conjecture,(
% 2.46/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.46/1.02    inference(negated_conjecture,[],[f17])).
% 2.46/1.02  
% 2.46/1.02  fof(f31,plain,(
% 2.46/1.02    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.46/1.02    inference(ennf_transformation,[],[f18])).
% 2.46/1.02  
% 2.46/1.02  fof(f32,plain,(
% 2.46/1.02    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.46/1.02    inference(flattening,[],[f31])).
% 2.46/1.02  
% 2.46/1.02  fof(f38,plain,(
% 2.46/1.02    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 2.46/1.02    introduced(choice_axiom,[])).
% 2.46/1.02  
% 2.46/1.02  fof(f39,plain,(
% 2.46/1.02    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 2.46/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f38])).
% 2.46/1.02  
% 2.46/1.02  fof(f71,plain,(
% 2.46/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.46/1.02    inference(cnf_transformation,[],[f39])).
% 2.46/1.02  
% 2.46/1.02  fof(f2,axiom,(
% 2.46/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f41,plain,(
% 2.46/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f2])).
% 2.46/1.02  
% 2.46/1.02  fof(f3,axiom,(
% 2.46/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f42,plain,(
% 2.46/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f3])).
% 2.46/1.02  
% 2.46/1.02  fof(f4,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f43,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f4])).
% 2.46/1.02  
% 2.46/1.02  fof(f74,plain,(
% 2.46/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.46/1.02    inference(definition_unfolding,[],[f42,f43])).
% 2.46/1.02  
% 2.46/1.02  fof(f75,plain,(
% 2.46/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.46/1.02    inference(definition_unfolding,[],[f41,f74])).
% 2.46/1.02  
% 2.46/1.02  fof(f90,plain,(
% 2.46/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.46/1.02    inference(definition_unfolding,[],[f71,f75])).
% 2.46/1.02  
% 2.46/1.02  fof(f14,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f27,plain,(
% 2.46/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.02    inference(ennf_transformation,[],[f14])).
% 2.46/1.02  
% 2.46/1.02  fof(f66,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f27])).
% 2.46/1.02  
% 2.46/1.02  fof(f13,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f26,plain,(
% 2.46/1.02    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.02    inference(ennf_transformation,[],[f13])).
% 2.46/1.02  
% 2.46/1.02  fof(f65,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f26])).
% 2.46/1.02  
% 2.46/1.02  fof(f7,axiom,(
% 2.46/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f37,plain,(
% 2.46/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.46/1.02    inference(nnf_transformation,[],[f7])).
% 2.46/1.02  
% 2.46/1.02  fof(f56,plain,(
% 2.46/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f37])).
% 2.46/1.02  
% 2.46/1.02  fof(f5,axiom,(
% 2.46/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f19,plain,(
% 2.46/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.46/1.02    inference(ennf_transformation,[],[f5])).
% 2.46/1.02  
% 2.46/1.02  fof(f33,plain,(
% 2.46/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.46/1.02    inference(nnf_transformation,[],[f19])).
% 2.46/1.02  
% 2.46/1.02  fof(f34,plain,(
% 2.46/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.46/1.02    inference(flattening,[],[f33])).
% 2.46/1.02  
% 2.46/1.02  fof(f44,plain,(
% 2.46/1.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f34])).
% 2.46/1.02  
% 2.46/1.02  fof(f84,plain,(
% 2.46/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.46/1.02    inference(definition_unfolding,[],[f44,f43,f74,f74,f74,f75,f75,f75,f43])).
% 2.46/1.02  
% 2.46/1.02  fof(f73,plain,(
% 2.46/1.02    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 2.46/1.02    inference(cnf_transformation,[],[f39])).
% 2.46/1.02  
% 2.46/1.02  fof(f89,plain,(
% 2.46/1.02    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 2.46/1.02    inference(definition_unfolding,[],[f73,f75,f75])).
% 2.46/1.02  
% 2.46/1.02  fof(f10,axiom,(
% 2.46/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f22,plain,(
% 2.46/1.02    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.46/1.02    inference(ennf_transformation,[],[f10])).
% 2.46/1.02  
% 2.46/1.02  fof(f23,plain,(
% 2.46/1.02    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.46/1.02    inference(flattening,[],[f22])).
% 2.46/1.02  
% 2.46/1.02  fof(f62,plain,(
% 2.46/1.02    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f23])).
% 2.46/1.02  
% 2.46/1.02  fof(f88,plain,(
% 2.46/1.02    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.46/1.02    inference(definition_unfolding,[],[f62,f75,f75])).
% 2.46/1.02  
% 2.46/1.02  fof(f69,plain,(
% 2.46/1.02    v1_funct_1(sK2)),
% 2.46/1.02    inference(cnf_transformation,[],[f39])).
% 2.46/1.02  
% 2.46/1.02  fof(f12,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f25,plain,(
% 2.46/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.02    inference(ennf_transformation,[],[f12])).
% 2.46/1.02  
% 2.46/1.02  fof(f64,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f25])).
% 2.46/1.02  
% 2.46/1.02  fof(f15,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f28,plain,(
% 2.46/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.02    inference(ennf_transformation,[],[f15])).
% 2.46/1.02  
% 2.46/1.02  fof(f67,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.02    inference(cnf_transformation,[],[f28])).
% 2.46/1.02  
% 2.46/1.02  fof(f9,axiom,(
% 2.46/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f20,plain,(
% 2.46/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.46/1.02    inference(ennf_transformation,[],[f9])).
% 2.46/1.02  
% 2.46/1.02  fof(f21,plain,(
% 2.46/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.46/1.02    inference(flattening,[],[f20])).
% 2.46/1.02  
% 2.46/1.02  fof(f60,plain,(
% 2.46/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f21])).
% 2.46/1.02  
% 2.46/1.02  fof(f48,plain,(
% 2.46/1.02    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_tarski(X2) != X3) )),
% 2.46/1.02    inference(cnf_transformation,[],[f34])).
% 2.46/1.02  
% 2.46/1.02  fof(f80,plain,(
% 2.46/1.02    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X3) )),
% 2.46/1.02    inference(definition_unfolding,[],[f48,f43,f75])).
% 2.46/1.02  
% 2.46/1.02  fof(f96,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X1,X2))) )),
% 2.46/1.02    inference(equality_resolution,[],[f80])).
% 2.46/1.02  
% 2.46/1.02  fof(f6,axiom,(
% 2.46/1.02    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f35,plain,(
% 2.46/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.46/1.02    inference(nnf_transformation,[],[f6])).
% 2.46/1.02  
% 2.46/1.02  fof(f36,plain,(
% 2.46/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.46/1.02    inference(flattening,[],[f35])).
% 2.46/1.02  
% 2.46/1.02  fof(f53,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f36])).
% 2.46/1.02  
% 2.46/1.02  fof(f87,plain,(
% 2.46/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 2.46/1.02    inference(definition_unfolding,[],[f53,f74])).
% 2.46/1.02  
% 2.46/1.02  fof(f16,axiom,(
% 2.46/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f29,plain,(
% 2.46/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.46/1.02    inference(ennf_transformation,[],[f16])).
% 2.46/1.02  
% 2.46/1.02  fof(f30,plain,(
% 2.46/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.46/1.02    inference(flattening,[],[f29])).
% 2.46/1.02  
% 2.46/1.02  fof(f68,plain,(
% 2.46/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f30])).
% 2.46/1.02  
% 2.46/1.02  fof(f70,plain,(
% 2.46/1.02    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 2.46/1.02    inference(cnf_transformation,[],[f39])).
% 2.46/1.02  
% 2.46/1.02  fof(f91,plain,(
% 2.46/1.02    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.46/1.02    inference(definition_unfolding,[],[f70,f75])).
% 2.46/1.02  
% 2.46/1.02  fof(f72,plain,(
% 2.46/1.02    k1_xboole_0 != sK1),
% 2.46/1.02    inference(cnf_transformation,[],[f39])).
% 2.46/1.02  
% 2.46/1.02  fof(f11,axiom,(
% 2.46/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f24,plain,(
% 2.46/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.46/1.02    inference(ennf_transformation,[],[f11])).
% 2.46/1.02  
% 2.46/1.02  fof(f63,plain,(
% 2.46/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f24])).
% 2.46/1.02  
% 2.46/1.02  fof(f8,axiom,(
% 2.46/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f59,plain,(
% 2.46/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.46/1.02    inference(cnf_transformation,[],[f8])).
% 2.46/1.02  
% 2.46/1.02  fof(f1,axiom,(
% 2.46/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.46/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.02  
% 2.46/1.02  fof(f40,plain,(
% 2.46/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.46/1.02    inference(cnf_transformation,[],[f1])).
% 2.46/1.02  
% 2.46/1.02  cnf(c_28,negated_conjecture,
% 2.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.46/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2839,plain,
% 2.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_23,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2841,plain,
% 2.46/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.46/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4419,plain,
% 2.46/1.02      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_2839,c_2841]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_22,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.02      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.46/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2842,plain,
% 2.46/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.46/1.02      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4619,plain,
% 2.46/1.02      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
% 2.46/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_4419,c_2842]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_33,plain,
% 2.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4769,plain,
% 2.46/1.02      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
% 2.46/1.02      inference(global_propositional_subsumption,[status(thm)],[c_4619,c_33]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_14,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.46/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2847,plain,
% 2.46/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.46/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4774,plain,
% 2.46/1.02      ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_4769,c_2847]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_9,plain,
% 2.46/1.02      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.46/1.02      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.46/1.02      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.46/1.02      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.46/1.02      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.46/1.02      | k1_xboole_0 = X0 ),
% 2.46/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2852,plain,
% 2.46/1.02      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.46/1.02      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.46/1.02      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.46/1.02      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.46/1.02      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.46/1.02      | k1_xboole_0 = X3
% 2.46/1.02      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5262,plain,
% 2.46/1.02      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
% 2.46/1.02      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_4774,c_2852]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_26,negated_conjecture,
% 2.46/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 2.46/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_19,plain,
% 2.46/1.02      ( ~ v1_funct_1(X0)
% 2.46/1.02      | ~ v1_relat_1(X0)
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.46/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_30,negated_conjecture,
% 2.46/1.02      ( v1_funct_1(sK2) ),
% 2.46/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_383,plain,
% 2.46/1.02      ( ~ v1_relat_1(X0)
% 2.46/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.46/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.46/1.02      | sK2 != X0 ),
% 2.46/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_384,plain,
% 2.46/1.02      ( ~ v1_relat_1(sK2)
% 2.46/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
% 2.46/1.02      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
% 2.46/1.02      inference(unflattening,[status(thm)],[c_383]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_385,plain,
% 2.46/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
% 2.46/1.02      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
% 2.46/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_387,plain,
% 2.46/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 2.46/1.02      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
% 2.46/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.46/1.02      inference(instantiation,[status(thm)],[c_385]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_21,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3032,plain,
% 2.46/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.46/1.02      | v1_relat_1(sK2) ),
% 2.46/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3033,plain,
% 2.46/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.46/1.02      | v1_relat_1(sK2) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_3032]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_24,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3050,plain,
% 2.46/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.46/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 2.46/1.02      inference(instantiation,[status(thm)],[c_24]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2239,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3035,plain,
% 2.46/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0
% 2.46/1.02      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 2.46/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0 ),
% 2.46/1.02      inference(instantiation,[status(thm)],[c_2239]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3276,plain,
% 2.46/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 2.46/1.02      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.46/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
% 2.46/1.02      inference(instantiation,[status(thm)],[c_3035]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5351,plain,
% 2.46/1.02      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.46/1.02      inference(global_propositional_subsumption,
% 2.46/1.02                [status(thm)],
% 2.46/1.02                [c_5262,c_28,c_33,c_26,c_387,c_3033,c_3050,c_3276]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_18,plain,
% 2.46/1.02      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.46/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2845,plain,
% 2.46/1.02      ( k1_relat_1(X0) != k1_xboole_0
% 2.46/1.02      | k1_xboole_0 = X0
% 2.46/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5369,plain,
% 2.46/1.02      ( sK2 = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_5351,c_2845]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5531,plain,
% 2.46/1.02      ( sK2 = k1_xboole_0 ),
% 2.46/1.02      inference(global_propositional_subsumption,
% 2.46/1.02                [status(thm)],
% 2.46/1.02                [c_5369,c_33,c_3033]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5,plain,
% 2.46/1.02      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) ),
% 2.46/1.02      inference(cnf_transformation,[],[f96]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2856,plain,
% 2.46/1.02      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_12,plain,
% 2.46/1.02      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
% 2.46/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2849,plain,
% 2.46/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.46/1.02      | r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3950,plain,
% 2.46/1.02      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_2856,c_2849]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2840,plain,
% 2.46/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.46/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4298,plain,
% 2.46/1.02      ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_2839,c_2840]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_25,plain,
% 2.46/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.02      | ~ r2_hidden(X3,X1)
% 2.46/1.02      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.46/1.02      | ~ v1_funct_1(X0)
% 2.46/1.02      | k1_xboole_0 = X2 ),
% 2.46/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_29,negated_conjecture,
% 2.46/1.02      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 2.46/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_362,plain,
% 2.46/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.02      | ~ r2_hidden(X3,X1)
% 2.46/1.02      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.46/1.02      | ~ v1_funct_1(X0)
% 2.46/1.02      | k2_enumset1(sK0,sK0,sK0,sK0) != X1
% 2.46/1.02      | sK1 != X2
% 2.46/1.02      | sK2 != X0
% 2.46/1.02      | k1_xboole_0 = X2 ),
% 2.46/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_363,plain,
% 2.46/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.46/1.02      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
% 2.46/1.02      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
% 2.46/1.02      | ~ v1_funct_1(sK2)
% 2.46/1.02      | k1_xboole_0 = sK1 ),
% 2.46/1.02      inference(unflattening,[status(thm)],[c_362]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_27,negated_conjecture,
% 2.46/1.02      ( k1_xboole_0 != sK1 ),
% 2.46/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_367,plain,
% 2.46/1.02      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
% 2.46/1.02      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ),
% 2.46/1.02      inference(global_propositional_subsumption,
% 2.46/1.02                [status(thm)],
% 2.46/1.02                [c_363,c_30,c_28,c_27]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2838,plain,
% 2.46/1.02      ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
% 2.46/1.02      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_20,plain,
% 2.46/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2844,plain,
% 2.46/1.02      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_3293,plain,
% 2.46/1.02      ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
% 2.46/1.02      | r1_tarski(k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_funct_1(sK2,X0)) != iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_2838,c_2844]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4561,plain,
% 2.46/1.02      ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top
% 2.46/1.02      | r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,X0)) != iProver_top ),
% 2.46/1.02      inference(demodulation,[status(thm)],[c_4298,c_3293]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_4682,plain,
% 2.46/1.02      ( r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK0)) != iProver_top ),
% 2.46/1.02      inference(superposition,[status(thm)],[c_3950,c_4561]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5538,plain,
% 2.46/1.02      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK0)) != iProver_top ),
% 2.46/1.02      inference(demodulation,[status(thm)],[c_5531,c_4682]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_15,plain,
% 2.46/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.46/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5570,plain,
% 2.46/1.02      ( r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK0)) != iProver_top ),
% 2.46/1.02      inference(light_normalisation,[status(thm)],[c_5538,c_15]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_0,plain,
% 2.46/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.46/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_2861,plain,
% 2.46/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.46/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.46/1.02  
% 2.46/1.02  cnf(c_5901,plain,
% 2.46/1.02      ( $false ),
% 2.46/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_5570,c_2861]) ).
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.02  
% 2.46/1.02  ------                               Statistics
% 2.46/1.02  
% 2.46/1.02  ------ General
% 2.46/1.02  
% 2.46/1.02  abstr_ref_over_cycles:                  0
% 2.46/1.02  abstr_ref_under_cycles:                 0
% 2.46/1.02  gc_basic_clause_elim:                   0
% 2.46/1.02  forced_gc_time:                         0
% 2.46/1.02  parsing_time:                           0.011
% 2.46/1.02  unif_index_cands_time:                  0.
% 2.46/1.02  unif_index_add_time:                    0.
% 2.46/1.02  orderings_time:                         0.
% 2.46/1.02  out_proof_time:                         0.014
% 2.46/1.02  total_time:                             0.224
% 2.46/1.02  num_of_symbols:                         49
% 2.46/1.02  num_of_terms:                           5186
% 2.46/1.02  
% 2.46/1.02  ------ Preprocessing
% 2.46/1.02  
% 2.46/1.02  num_of_splits:                          0
% 2.46/1.02  num_of_split_atoms:                     0
% 2.46/1.02  num_of_reused_defs:                     0
% 2.46/1.02  num_eq_ax_congr_red:                    10
% 2.46/1.02  num_of_sem_filtered_clauses:            1
% 2.46/1.02  num_of_subtypes:                        0
% 2.46/1.02  monotx_restored_types:                  0
% 2.46/1.02  sat_num_of_epr_types:                   0
% 2.46/1.02  sat_num_of_non_cyclic_types:            0
% 2.46/1.02  sat_guarded_non_collapsed_types:        0
% 2.46/1.02  num_pure_diseq_elim:                    0
% 2.46/1.02  simp_replaced_by:                       0
% 2.46/1.02  res_preprocessed:                       145
% 2.46/1.02  prep_upred:                             0
% 2.46/1.02  prep_unflattend:                        164
% 2.46/1.02  smt_new_axioms:                         0
% 2.46/1.02  pred_elim_cands:                        4
% 2.46/1.02  pred_elim:                              2
% 2.46/1.02  pred_elim_cl:                           2
% 2.46/1.02  pred_elim_cycles:                       6
% 2.46/1.02  merged_defs:                            8
% 2.46/1.02  merged_defs_ncl:                        0
% 2.46/1.02  bin_hyper_res:                          8
% 2.46/1.02  prep_cycles:                            4
% 2.46/1.02  pred_elim_time:                         0.031
% 2.46/1.02  splitting_time:                         0.
% 2.46/1.02  sem_filter_time:                        0.
% 2.46/1.02  monotx_time:                            0.
% 2.46/1.02  subtype_inf_time:                       0.
% 2.46/1.02  
% 2.46/1.02  ------ Problem properties
% 2.46/1.02  
% 2.46/1.02  clauses:                                29
% 2.46/1.02  conjectures:                            3
% 2.46/1.02  epr:                                    3
% 2.46/1.02  horn:                                   28
% 2.46/1.02  ground:                                 5
% 2.46/1.02  unary:                                  14
% 2.46/1.02  binary:                                 10
% 2.46/1.02  lits:                                   55
% 2.46/1.02  lits_eq:                                20
% 2.46/1.02  fd_pure:                                0
% 2.46/1.02  fd_pseudo:                              0
% 2.46/1.02  fd_cond:                                2
% 2.46/1.02  fd_pseudo_cond:                         1
% 2.46/1.02  ac_symbols:                             0
% 2.46/1.02  
% 2.46/1.02  ------ Propositional Solver
% 2.46/1.02  
% 2.46/1.02  prop_solver_calls:                      27
% 2.46/1.02  prop_fast_solver_calls:                 1034
% 2.46/1.02  smt_solver_calls:                       0
% 2.46/1.02  smt_fast_solver_calls:                  0
% 2.46/1.02  prop_num_of_clauses:                    1375
% 2.46/1.02  prop_preprocess_simplified:             6653
% 2.46/1.02  prop_fo_subsumed:                       7
% 2.46/1.02  prop_solver_time:                       0.
% 2.46/1.02  smt_solver_time:                        0.
% 2.46/1.02  smt_fast_solver_time:                   0.
% 2.46/1.02  prop_fast_solver_time:                  0.
% 2.46/1.02  prop_unsat_core_time:                   0.
% 2.46/1.02  
% 2.46/1.02  ------ QBF
% 2.46/1.02  
% 2.46/1.02  qbf_q_res:                              0
% 2.46/1.02  qbf_num_tautologies:                    0
% 2.46/1.02  qbf_prep_cycles:                        0
% 2.46/1.02  
% 2.46/1.02  ------ BMC1
% 2.46/1.02  
% 2.46/1.02  bmc1_current_bound:                     -1
% 2.46/1.02  bmc1_last_solved_bound:                 -1
% 2.46/1.02  bmc1_unsat_core_size:                   -1
% 2.46/1.02  bmc1_unsat_core_parents_size:           -1
% 2.46/1.02  bmc1_merge_next_fun:                    0
% 2.46/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.02  
% 2.46/1.02  ------ Instantiation
% 2.46/1.02  
% 2.46/1.02  inst_num_of_clauses:                    462
% 2.46/1.02  inst_num_in_passive:                    62
% 2.46/1.02  inst_num_in_active:                     296
% 2.46/1.02  inst_num_in_unprocessed:                104
% 2.46/1.02  inst_num_of_loops:                      310
% 2.46/1.02  inst_num_of_learning_restarts:          0
% 2.46/1.02  inst_num_moves_active_passive:          12
% 2.46/1.02  inst_lit_activity:                      0
% 2.46/1.02  inst_lit_activity_moves:                0
% 2.46/1.02  inst_num_tautologies:                   0
% 2.46/1.02  inst_num_prop_implied:                  0
% 2.46/1.02  inst_num_existing_simplified:           0
% 2.46/1.02  inst_num_eq_res_simplified:             0
% 2.46/1.02  inst_num_child_elim:                    0
% 2.46/1.02  inst_num_of_dismatching_blockings:      445
% 2.46/1.02  inst_num_of_non_proper_insts:           634
% 2.46/1.02  inst_num_of_duplicates:                 0
% 2.46/1.02  inst_inst_num_from_inst_to_res:         0
% 2.46/1.02  inst_dismatching_checking_time:         0.
% 2.46/1.02  
% 2.46/1.02  ------ Resolution
% 2.46/1.02  
% 2.46/1.02  res_num_of_clauses:                     0
% 2.46/1.02  res_num_in_passive:                     0
% 2.46/1.02  res_num_in_active:                      0
% 2.46/1.02  res_num_of_loops:                       149
% 2.46/1.02  res_forward_subset_subsumed:            92
% 2.46/1.02  res_backward_subset_subsumed:           2
% 2.46/1.02  res_forward_subsumed:                   8
% 2.46/1.02  res_backward_subsumed:                  0
% 2.46/1.02  res_forward_subsumption_resolution:     0
% 2.46/1.02  res_backward_subsumption_resolution:    0
% 2.46/1.02  res_clause_to_clause_subsumption:       1078
% 2.46/1.02  res_orphan_elimination:                 0
% 2.46/1.02  res_tautology_del:                      114
% 2.46/1.02  res_num_eq_res_simplified:              0
% 2.46/1.02  res_num_sel_changes:                    0
% 2.46/1.02  res_moves_from_active_to_pass:          0
% 2.46/1.02  
% 2.46/1.02  ------ Superposition
% 2.46/1.02  
% 2.46/1.02  sup_time_total:                         0.
% 2.46/1.02  sup_time_generating:                    0.
% 2.46/1.02  sup_time_sim_full:                      0.
% 2.46/1.02  sup_time_sim_immed:                     0.
% 2.46/1.02  
% 2.46/1.02  sup_num_of_clauses:                     61
% 2.46/1.02  sup_num_in_active:                      41
% 2.46/1.02  sup_num_in_passive:                     20
% 2.46/1.02  sup_num_of_loops:                       61
% 2.46/1.02  sup_fw_superposition:                   56
% 2.46/1.02  sup_bw_superposition:                   22
% 2.46/1.02  sup_immediate_simplified:               15
% 2.46/1.02  sup_given_eliminated:                   0
% 2.46/1.02  comparisons_done:                       0
% 2.46/1.02  comparisons_avoided:                    0
% 2.46/1.02  
% 2.46/1.02  ------ Simplifications
% 2.46/1.02  
% 2.46/1.02  
% 2.46/1.02  sim_fw_subset_subsumed:                 1
% 2.46/1.02  sim_bw_subset_subsumed:                 0
% 2.46/1.02  sim_fw_subsumed:                        5
% 2.46/1.02  sim_bw_subsumed:                        0
% 2.46/1.02  sim_fw_subsumption_res:                 1
% 2.46/1.02  sim_bw_subsumption_res:                 0
% 2.46/1.02  sim_tautology_del:                      3
% 2.46/1.02  sim_eq_tautology_del:                   9
% 2.46/1.02  sim_eq_res_simp:                        0
% 2.46/1.02  sim_fw_demodulated:                     0
% 2.46/1.02  sim_bw_demodulated:                     20
% 2.46/1.02  sim_light_normalised:                   10
% 2.46/1.02  sim_joinable_taut:                      0
% 2.46/1.02  sim_joinable_simp:                      0
% 2.46/1.02  sim_ac_normalised:                      0
% 2.46/1.02  sim_smt_subsumption:                    0
% 2.46/1.02  
%------------------------------------------------------------------------------
