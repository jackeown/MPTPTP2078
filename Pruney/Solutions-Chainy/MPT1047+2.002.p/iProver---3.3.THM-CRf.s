%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:51 EST 2020

% Result     : Theorem 19.56s
% Output     : CNFRefutation 19.56s
% Verified   : 
% Statistics : Number of formulae       :  311 (17279 expanded)
%              Number of clauses        :  197 (3444 expanded)
%              Number of leaves         :   30 (4888 expanded)
%              Depth                    :   32
%              Number of atoms          : 1129 (59452 expanded)
%              Number of equality atoms :  600 (22236 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK9) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK9,X0,k1_tarski(X1))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
          & v1_funct_2(X3,sK6,k1_tarski(sK7))
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f36,f59,f58])).

fof(f109,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f111,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f112,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f111])).

fof(f123,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f109,f112])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f60])).

fof(f108,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f60])).

fof(f124,plain,(
    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f108,f112])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f69,f112])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f104,f112,f112,f112,f112,f112])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f70,f112])).

fof(f106,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f125,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f106,f112])).

fof(f105,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f60])).

fof(f110,plain,(
    k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,(
    k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(definition_unfolding,[],[f110,f112,f112])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f37,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f26,f38,f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f52,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f53,f56,f55,f54])).

fof(f90,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f90])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f100,f112,f112])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f78,f111])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f77,f111])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f76,f111])).

fof(f87,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK5(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f112])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_5093,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5098,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10818,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
    | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | v1_partfun1(sK9,sK6) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5098])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_49,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_50,plain,
    ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_11397,plain,
    ( v1_partfun1(sK9,sK6) = iProver_top
    | k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10818,c_49,c_50])).

cnf(c_11398,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
    | v1_partfun1(sK9,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_11397])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_5117,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5096,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5096])).

cnf(c_9584,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9226,c_49])).

cnf(c_9585,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9584])).

cnf(c_9594,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_9585])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
    | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
    | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_590,plain,
    ( ~ v1_funct_2(X0,X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_funct_2(X3,X1,k2_enumset1(X2,X2,X2,X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X3 != X7
    | X0 != X4
    | X1 != X5
    | X4 = X7
    | k2_enumset1(X2,X2,X2,X2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_40])).

cnf(c_591,plain,
    ( ~ v1_funct_2(X0,X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_funct_2(X3,X1,k2_enumset1(X2,X2,X2,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X0 = X3 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_5086,plain,
    ( X0 = X1
    | v1_funct_2(X0,X2,k2_enumset1(X3,X3,X3,X3)) != iProver_top
    | v1_funct_2(X1,X2,k2_enumset1(X3,X3,X3,X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_9698,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9594,c_5086])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5094,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7678,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5094])).

cnf(c_7984,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7678,c_49])).

cnf(c_7985,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7984])).

cnf(c_7991,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_7985])).

cnf(c_38,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5095,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8442,plain,
    ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5095])).

cnf(c_8676,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8442,c_49])).

cnf(c_8677,plain,
    ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8676])).

cnf(c_8685,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8677])).

cnf(c_45494,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9698,c_7991,c_8685])).

cnf(c_45495,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_45494])).

cnf(c_45502,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
    | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_45495])).

cnf(c_45545,plain,
    ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ v1_funct_1(sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45502])).

cnf(c_46389,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45502,c_49,c_50])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_46398,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK9 != X0 ),
    inference(superposition,[status(thm)],[c_46389,c_5])).

cnf(c_47012,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(sK9,sK9,sK9,sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_46398])).

cnf(c_47656,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK9,sK9,sK9,sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
    inference(superposition,[status(thm)],[c_47012,c_46389])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_5090,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_9227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_5096])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_47,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_9611,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9227,c_47])).

cnf(c_9612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9611])).

cnf(c_9621,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_9612])).

cnf(c_9731,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9621,c_5086])).

cnf(c_7679,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_5094])).

cnf(c_7999,plain,
    ( v1_funct_1(X0) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7679,c_47])).

cnf(c_8000,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | v1_funct_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7999])).

cnf(c_8006,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8000])).

cnf(c_8443,plain,
    ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_5095])).

cnf(c_8815,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
    | v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8443,c_47])).

cnf(c_8816,plain,
    ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8815])).

cnf(c_8824,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_8816])).

cnf(c_59665,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9731,c_8006,c_8824])).

cnf(c_59666,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
    | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_59665])).

cnf(c_59673,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9
    | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_59666])).

cnf(c_59719,plain,
    ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ v1_funct_1(sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_59673])).

cnf(c_60484,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59673,c_49,c_50])).

cnf(c_41,negated_conjecture,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_60638,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK9,sK9,sK9,sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
    inference(superposition,[status(thm)],[c_60484,c_41])).

cnf(c_61059,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
    inference(superposition,[status(thm)],[c_47656,c_60638])).

cnf(c_4245,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5169,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != X0
    | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_5192,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
    | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5169])).

cnf(c_4244,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5246,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4244])).

cnf(c_61064,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) = sK9 ),
    inference(equality_resolution,[status(thm)],[c_60638])).

cnf(c_61197,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_61064,c_5])).

cnf(c_61215,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61059,c_41,c_5192,c_5246,c_61197])).

cnf(c_33,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_546,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X1 != X4
    | X2 != X5
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_20])).

cnf(c_547,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_5088,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ r1_partfun1(X0,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_5105,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12070,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5105])).

cnf(c_12362,plain,
    ( r2_hidden(sK9,X1) = iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12070,c_49])).

cnf(c_12363,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_12362])).

cnf(c_12368,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_12363])).

cnf(c_36,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5097,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10031,plain,
    ( r1_partfun1(X0,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_5097])).

cnf(c_12493,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12368,c_49,c_10031])).

cnf(c_12502,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_12493])).

cnf(c_12720,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12502,c_47])).

cnf(c_12721,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12720])).

cnf(c_61322,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61215,c_12721])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_135,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_136,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5193,plain,
    ( X0 != X1
    | k2_enumset1(sK9,sK9,sK9,sK9) != X1
    | k2_enumset1(sK9,sK9,sK9,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_5283,plain,
    ( X0 != k2_enumset1(sK9,sK9,sK9,sK9)
    | k2_enumset1(sK9,sK9,sK9,sK9) = X0
    | k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5193])).

cnf(c_5284,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
    | k2_enumset1(sK9,sK9,sK9,sK9) = k1_xboole_0
    | k1_xboole_0 != k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5283])).

cnf(c_5353,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != X0
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X0
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_5354,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k1_xboole_0
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5353])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5363,plain,
    ( ~ r2_hidden(sK9,k1_xboole_0)
    | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5364,plain,
    ( r2_hidden(sK9,k1_xboole_0) != iProver_top
    | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5363])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5770,plain,
    ( ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK9,sK9,sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5771,plain,
    ( k1_xboole_0 = k2_enumset1(sK9,sK9,sK9,sK9)
    | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5770])).

cnf(c_5887,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_4244])).

cnf(c_12501,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_12493])).

cnf(c_12712,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12501,c_49])).

cnf(c_12713,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12712])).

cnf(c_4248,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5812,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK9,k1_xboole_0)
    | sK9 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_4248])).

cnf(c_7084,plain,
    ( ~ r2_hidden(sK9,X0)
    | r2_hidden(sK9,k1_xboole_0)
    | sK9 != sK9
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_5812])).

cnf(c_34277,plain,
    ( ~ r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9))
    | r2_hidden(sK9,k1_xboole_0)
    | sK9 != sK9
    | k1_xboole_0 != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) ),
    inference(instantiation,[status(thm)],[c_7084])).

cnf(c_34284,plain,
    ( sK9 != sK9
    | k1_xboole_0 != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34277])).

cnf(c_37002,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_37003,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k1_xboole_0
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_37002])).

cnf(c_12071,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK8,sK6) != iProver_top
    | r1_partfun1(X0,sK8) != iProver_top
    | r2_hidden(sK8,X1) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_5105])).

cnf(c_12482,plain,
    ( r2_hidden(sK8,X1) = iProver_top
    | r1_partfun1(X0,sK8) != iProver_top
    | v1_partfun1(sK8,sK6) != iProver_top
    | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12071,c_47])).

cnf(c_12483,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK8,sK6) != iProver_top
    | r1_partfun1(X0,sK8) != iProver_top
    | r2_hidden(sK8,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_12482])).

cnf(c_12488,plain,
    ( v1_partfun1(sK8,sK6) != iProver_top
    | r1_partfun1(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_12483])).

cnf(c_10032,plain,
    ( r1_partfun1(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_5097])).

cnf(c_12808,plain,
    ( v1_partfun1(sK8,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12488,c_47,c_10032])).

cnf(c_12817,plain,
    ( v1_partfun1(sK8,sK6) != iProver_top
    | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_12808])).

cnf(c_12970,plain,
    ( r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
    | v1_partfun1(sK8,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12817,c_47])).

cnf(c_12971,plain,
    ( v1_partfun1(sK8,sK6) != iProver_top
    | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12970])).

cnf(c_5116,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_5115,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_50171,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
    | r2_hidden(sK9,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_47656,c_5115])).

cnf(c_56459,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5116,c_50171])).

cnf(c_56498,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),sK8) = sK9
    | v1_partfun1(sK8,sK6) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12971,c_56459])).

cnf(c_51,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_46397,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46389,c_5117])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_5818,plain,
    ( r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5819,plain,
    ( r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5818])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_5864,plain,
    ( r2_hidden(sK9,X0)
    | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,X1),X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7062,plain,
    ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,X0))
    | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,X0),k2_enumset1(sK9,sK9,sK9,X0)) ),
    inference(instantiation,[status(thm)],[c_5864])).

cnf(c_8409,plain,
    ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
    | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) ),
    inference(instantiation,[status(thm)],[c_7062])).

cnf(c_8410,plain,
    ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9)) = iProver_top
    | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8409])).

cnf(c_5872,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK9,X2)
    | X2 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_4248])).

cnf(c_9054,plain,
    ( ~ r2_hidden(sK9,X0)
    | r2_hidden(sK9,X1)
    | X1 != X0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_5872])).

cnf(c_14786,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
    | X0 != k2_enumset1(sK9,sK9,sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_9054])).

cnf(c_31359,plain,
    ( ~ r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9))
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_14786])).

cnf(c_31360,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
    | sK9 != sK9
    | r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9)) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31359])).

cnf(c_48312,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46397,c_5819,c_5887,c_8410,c_31360,c_47012])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK5(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5102,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7282,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_5102])).

cnf(c_17097,plain,
    ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_7282])).

cnf(c_17586,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17097,c_49])).

cnf(c_17587,plain,
    ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0
    | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17586])).

cnf(c_48325,plain,
    ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK9
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48312,c_17587])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_partfun1(sK5(X0,X1,X2,X4),X1)
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5103,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7804,plain,
    ( v1_partfun1(sK5(X0,X1,X2,X3),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_5103])).

cnf(c_48345,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | v1_partfun1(sK9,sK6) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_48325,c_7804])).

cnf(c_59410,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56498,c_47,c_49,c_51,c_12502,c_48312,c_48345])).

cnf(c_61220,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61215,c_59410])).

cnf(c_62354,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61322,c_49,c_41,c_135,c_136,c_5192,c_5246,c_5284,c_5354,c_5364,c_5771,c_5887,c_12501,c_34284,c_37003,c_61197,c_61220])).

cnf(c_62358,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11398,c_62354])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_62524,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_62358,c_11])).

cnf(c_62559,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_62524,c_8])).

cnf(c_62560,plain,
    ( k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_62559])).

cnf(c_62563,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_62560,c_62358])).

cnf(c_62400,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62358,c_5093])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_62404,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62400,c_7])).

cnf(c_5727,plain,
    ( X0 != X1
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X1
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_11443,plain,
    ( k2_enumset1(X0,X1,X2,X3) != X4
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X4
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_5727])).

cnf(c_11444,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11443])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10751,plain,
    ( r1_tarski(k1_xboole_0,sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10752,plain,
    ( r1_tarski(k1_xboole_0,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10751])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6215,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6216,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6215])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5492,plain,
    ( ~ r1_tarski(X0,sK9)
    | ~ r1_tarski(sK9,X0)
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5493,plain,
    ( sK9 = X0
    | r1_tarski(X0,sK9) != iProver_top
    | r1_tarski(sK9,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5492])).

cnf(c_5495,plain,
    ( sK9 = k1_xboole_0
    | r1_tarski(sK9,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5493])).

cnf(c_4247,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_5292,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(X0,X1,X2,X3)
    | sK9 != X0
    | sK9 != X1
    | sK9 != X2
    | sK9 != X3 ),
    inference(instantiation,[status(thm)],[c_4247])).

cnf(c_5293,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK9 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5292])).

cnf(c_5194,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(X0,X1,X2,X3)
    | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_5169])).

cnf(c_5195,plain,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5194])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62563,c_62404,c_61197,c_11444,c_10752,c_6216,c_5495,c_5293,c_5246,c_5195,c_5192,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.56/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.56/2.98  
% 19.56/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.56/2.98  
% 19.56/2.98  ------  iProver source info
% 19.56/2.98  
% 19.56/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.56/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.56/2.98  git: non_committed_changes: false
% 19.56/2.98  git: last_make_outside_of_git: false
% 19.56/2.98  
% 19.56/2.98  ------ 
% 19.56/2.98  
% 19.56/2.98  ------ Input Options
% 19.56/2.98  
% 19.56/2.98  --out_options                           all
% 19.56/2.98  --tptp_safe_out                         true
% 19.56/2.98  --problem_path                          ""
% 19.56/2.98  --include_path                          ""
% 19.56/2.98  --clausifier                            res/vclausify_rel
% 19.56/2.98  --clausifier_options                    ""
% 19.56/2.98  --stdin                                 false
% 19.56/2.98  --stats_out                             all
% 19.56/2.98  
% 19.56/2.98  ------ General Options
% 19.56/2.98  
% 19.56/2.98  --fof                                   false
% 19.56/2.98  --time_out_real                         305.
% 19.56/2.98  --time_out_virtual                      -1.
% 19.56/2.98  --symbol_type_check                     false
% 19.56/2.98  --clausify_out                          false
% 19.56/2.98  --sig_cnt_out                           false
% 19.56/2.98  --trig_cnt_out                          false
% 19.56/2.98  --trig_cnt_out_tolerance                1.
% 19.56/2.98  --trig_cnt_out_sk_spl                   false
% 19.56/2.98  --abstr_cl_out                          false
% 19.56/2.98  
% 19.56/2.98  ------ Global Options
% 19.56/2.98  
% 19.56/2.98  --schedule                              default
% 19.56/2.98  --add_important_lit                     false
% 19.56/2.98  --prop_solver_per_cl                    1000
% 19.56/2.98  --min_unsat_core                        false
% 19.56/2.98  --soft_assumptions                      false
% 19.56/2.98  --soft_lemma_size                       3
% 19.56/2.98  --prop_impl_unit_size                   0
% 19.56/2.98  --prop_impl_unit                        []
% 19.56/2.98  --share_sel_clauses                     true
% 19.56/2.98  --reset_solvers                         false
% 19.56/2.98  --bc_imp_inh                            [conj_cone]
% 19.56/2.98  --conj_cone_tolerance                   3.
% 19.56/2.98  --extra_neg_conj                        none
% 19.56/2.98  --large_theory_mode                     true
% 19.56/2.98  --prolific_symb_bound                   200
% 19.56/2.98  --lt_threshold                          2000
% 19.56/2.98  --clause_weak_htbl                      true
% 19.56/2.98  --gc_record_bc_elim                     false
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing Options
% 19.56/2.98  
% 19.56/2.98  --preprocessing_flag                    true
% 19.56/2.98  --time_out_prep_mult                    0.1
% 19.56/2.98  --splitting_mode                        input
% 19.56/2.98  --splitting_grd                         true
% 19.56/2.98  --splitting_cvd                         false
% 19.56/2.98  --splitting_cvd_svl                     false
% 19.56/2.98  --splitting_nvd                         32
% 19.56/2.98  --sub_typing                            true
% 19.56/2.98  --prep_gs_sim                           true
% 19.56/2.98  --prep_unflatten                        true
% 19.56/2.98  --prep_res_sim                          true
% 19.56/2.98  --prep_upred                            true
% 19.56/2.98  --prep_sem_filter                       exhaustive
% 19.56/2.98  --prep_sem_filter_out                   false
% 19.56/2.98  --pred_elim                             true
% 19.56/2.98  --res_sim_input                         true
% 19.56/2.98  --eq_ax_congr_red                       true
% 19.56/2.98  --pure_diseq_elim                       true
% 19.56/2.98  --brand_transform                       false
% 19.56/2.98  --non_eq_to_eq                          false
% 19.56/2.98  --prep_def_merge                        true
% 19.56/2.98  --prep_def_merge_prop_impl              false
% 19.56/2.98  --prep_def_merge_mbd                    true
% 19.56/2.98  --prep_def_merge_tr_red                 false
% 19.56/2.98  --prep_def_merge_tr_cl                  false
% 19.56/2.98  --smt_preprocessing                     true
% 19.56/2.98  --smt_ac_axioms                         fast
% 19.56/2.98  --preprocessed_out                      false
% 19.56/2.98  --preprocessed_stats                    false
% 19.56/2.98  
% 19.56/2.98  ------ Abstraction refinement Options
% 19.56/2.98  
% 19.56/2.98  --abstr_ref                             []
% 19.56/2.98  --abstr_ref_prep                        false
% 19.56/2.98  --abstr_ref_until_sat                   false
% 19.56/2.98  --abstr_ref_sig_restrict                funpre
% 19.56/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.56/2.98  --abstr_ref_under                       []
% 19.56/2.98  
% 19.56/2.98  ------ SAT Options
% 19.56/2.98  
% 19.56/2.98  --sat_mode                              false
% 19.56/2.98  --sat_fm_restart_options                ""
% 19.56/2.98  --sat_gr_def                            false
% 19.56/2.98  --sat_epr_types                         true
% 19.56/2.98  --sat_non_cyclic_types                  false
% 19.56/2.98  --sat_finite_models                     false
% 19.56/2.98  --sat_fm_lemmas                         false
% 19.56/2.98  --sat_fm_prep                           false
% 19.56/2.98  --sat_fm_uc_incr                        true
% 19.56/2.98  --sat_out_model                         small
% 19.56/2.98  --sat_out_clauses                       false
% 19.56/2.98  
% 19.56/2.98  ------ QBF Options
% 19.56/2.98  
% 19.56/2.98  --qbf_mode                              false
% 19.56/2.98  --qbf_elim_univ                         false
% 19.56/2.98  --qbf_dom_inst                          none
% 19.56/2.98  --qbf_dom_pre_inst                      false
% 19.56/2.98  --qbf_sk_in                             false
% 19.56/2.98  --qbf_pred_elim                         true
% 19.56/2.98  --qbf_split                             512
% 19.56/2.98  
% 19.56/2.98  ------ BMC1 Options
% 19.56/2.98  
% 19.56/2.98  --bmc1_incremental                      false
% 19.56/2.98  --bmc1_axioms                           reachable_all
% 19.56/2.98  --bmc1_min_bound                        0
% 19.56/2.98  --bmc1_max_bound                        -1
% 19.56/2.98  --bmc1_max_bound_default                -1
% 19.56/2.98  --bmc1_symbol_reachability              true
% 19.56/2.98  --bmc1_property_lemmas                  false
% 19.56/2.98  --bmc1_k_induction                      false
% 19.56/2.98  --bmc1_non_equiv_states                 false
% 19.56/2.98  --bmc1_deadlock                         false
% 19.56/2.98  --bmc1_ucm                              false
% 19.56/2.98  --bmc1_add_unsat_core                   none
% 19.56/2.98  --bmc1_unsat_core_children              false
% 19.56/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.56/2.98  --bmc1_out_stat                         full
% 19.56/2.98  --bmc1_ground_init                      false
% 19.56/2.98  --bmc1_pre_inst_next_state              false
% 19.56/2.98  --bmc1_pre_inst_state                   false
% 19.56/2.98  --bmc1_pre_inst_reach_state             false
% 19.56/2.98  --bmc1_out_unsat_core                   false
% 19.56/2.98  --bmc1_aig_witness_out                  false
% 19.56/2.98  --bmc1_verbose                          false
% 19.56/2.98  --bmc1_dump_clauses_tptp                false
% 19.56/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.56/2.98  --bmc1_dump_file                        -
% 19.56/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.56/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.56/2.98  --bmc1_ucm_extend_mode                  1
% 19.56/2.98  --bmc1_ucm_init_mode                    2
% 19.56/2.98  --bmc1_ucm_cone_mode                    none
% 19.56/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.56/2.98  --bmc1_ucm_relax_model                  4
% 19.56/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.56/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.56/2.98  --bmc1_ucm_layered_model                none
% 19.56/2.98  --bmc1_ucm_max_lemma_size               10
% 19.56/2.98  
% 19.56/2.98  ------ AIG Options
% 19.56/2.98  
% 19.56/2.98  --aig_mode                              false
% 19.56/2.98  
% 19.56/2.98  ------ Instantiation Options
% 19.56/2.98  
% 19.56/2.98  --instantiation_flag                    true
% 19.56/2.98  --inst_sos_flag                         true
% 19.56/2.98  --inst_sos_phase                        true
% 19.56/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.56/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.56/2.98  --inst_lit_sel_side                     num_symb
% 19.56/2.98  --inst_solver_per_active                1400
% 19.56/2.98  --inst_solver_calls_frac                1.
% 19.56/2.98  --inst_passive_queue_type               priority_queues
% 19.56/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.56/2.98  --inst_passive_queues_freq              [25;2]
% 19.56/2.98  --inst_dismatching                      true
% 19.56/2.98  --inst_eager_unprocessed_to_passive     true
% 19.56/2.98  --inst_prop_sim_given                   true
% 19.56/2.98  --inst_prop_sim_new                     false
% 19.56/2.98  --inst_subs_new                         false
% 19.56/2.98  --inst_eq_res_simp                      false
% 19.56/2.98  --inst_subs_given                       false
% 19.56/2.98  --inst_orphan_elimination               true
% 19.56/2.98  --inst_learning_loop_flag               true
% 19.56/2.98  --inst_learning_start                   3000
% 19.56/2.98  --inst_learning_factor                  2
% 19.56/2.98  --inst_start_prop_sim_after_learn       3
% 19.56/2.98  --inst_sel_renew                        solver
% 19.56/2.98  --inst_lit_activity_flag                true
% 19.56/2.98  --inst_restr_to_given                   false
% 19.56/2.98  --inst_activity_threshold               500
% 19.56/2.98  --inst_out_proof                        true
% 19.56/2.98  
% 19.56/2.98  ------ Resolution Options
% 19.56/2.98  
% 19.56/2.98  --resolution_flag                       true
% 19.56/2.98  --res_lit_sel                           adaptive
% 19.56/2.98  --res_lit_sel_side                      none
% 19.56/2.98  --res_ordering                          kbo
% 19.56/2.98  --res_to_prop_solver                    active
% 19.56/2.98  --res_prop_simpl_new                    false
% 19.56/2.98  --res_prop_simpl_given                  true
% 19.56/2.98  --res_passive_queue_type                priority_queues
% 19.56/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.56/2.98  --res_passive_queues_freq               [15;5]
% 19.56/2.98  --res_forward_subs                      full
% 19.56/2.98  --res_backward_subs                     full
% 19.56/2.98  --res_forward_subs_resolution           true
% 19.56/2.98  --res_backward_subs_resolution          true
% 19.56/2.98  --res_orphan_elimination                true
% 19.56/2.98  --res_time_limit                        2.
% 19.56/2.98  --res_out_proof                         true
% 19.56/2.98  
% 19.56/2.98  ------ Superposition Options
% 19.56/2.98  
% 19.56/2.98  --superposition_flag                    true
% 19.56/2.98  --sup_passive_queue_type                priority_queues
% 19.56/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.56/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.56/2.98  --demod_completeness_check              fast
% 19.56/2.98  --demod_use_ground                      true
% 19.56/2.98  --sup_to_prop_solver                    passive
% 19.56/2.98  --sup_prop_simpl_new                    true
% 19.56/2.98  --sup_prop_simpl_given                  true
% 19.56/2.98  --sup_fun_splitting                     true
% 19.56/2.98  --sup_smt_interval                      50000
% 19.56/2.98  
% 19.56/2.98  ------ Superposition Simplification Setup
% 19.56/2.98  
% 19.56/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.56/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.56/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.56/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.56/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.56/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.56/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.56/2.98  --sup_immed_triv                        [TrivRules]
% 19.56/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_immed_bw_main                     []
% 19.56/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.56/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.56/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_input_bw                          []
% 19.56/2.98  
% 19.56/2.98  ------ Combination Options
% 19.56/2.98  
% 19.56/2.98  --comb_res_mult                         3
% 19.56/2.98  --comb_sup_mult                         2
% 19.56/2.98  --comb_inst_mult                        10
% 19.56/2.98  
% 19.56/2.98  ------ Debug Options
% 19.56/2.98  
% 19.56/2.98  --dbg_backtrace                         false
% 19.56/2.98  --dbg_dump_prop_clauses                 false
% 19.56/2.98  --dbg_dump_prop_clauses_file            -
% 19.56/2.98  --dbg_out_stat                          false
% 19.56/2.98  ------ Parsing...
% 19.56/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.56/2.98  ------ Proving...
% 19.56/2.98  ------ Problem Properties 
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  clauses                                 43
% 19.56/2.98  conjectures                             6
% 19.56/2.98  EPR                                     6
% 19.56/2.98  Horn                                    34
% 19.56/2.98  unary                                   10
% 19.56/2.98  binary                                  7
% 19.56/2.98  lits                                    121
% 19.56/2.98  lits eq                                 22
% 19.56/2.98  fd_pure                                 0
% 19.56/2.98  fd_pseudo                               0
% 19.56/2.98  fd_cond                                 5
% 19.56/2.98  fd_pseudo_cond                          5
% 19.56/2.98  AC symbols                              0
% 19.56/2.98  
% 19.56/2.98  ------ Schedule dynamic 5 is on 
% 19.56/2.98  
% 19.56/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  ------ 
% 19.56/2.98  Current options:
% 19.56/2.98  ------ 
% 19.56/2.98  
% 19.56/2.98  ------ Input Options
% 19.56/2.98  
% 19.56/2.98  --out_options                           all
% 19.56/2.98  --tptp_safe_out                         true
% 19.56/2.98  --problem_path                          ""
% 19.56/2.98  --include_path                          ""
% 19.56/2.98  --clausifier                            res/vclausify_rel
% 19.56/2.98  --clausifier_options                    ""
% 19.56/2.98  --stdin                                 false
% 19.56/2.98  --stats_out                             all
% 19.56/2.98  
% 19.56/2.98  ------ General Options
% 19.56/2.98  
% 19.56/2.98  --fof                                   false
% 19.56/2.98  --time_out_real                         305.
% 19.56/2.98  --time_out_virtual                      -1.
% 19.56/2.98  --symbol_type_check                     false
% 19.56/2.98  --clausify_out                          false
% 19.56/2.98  --sig_cnt_out                           false
% 19.56/2.98  --trig_cnt_out                          false
% 19.56/2.98  --trig_cnt_out_tolerance                1.
% 19.56/2.98  --trig_cnt_out_sk_spl                   false
% 19.56/2.98  --abstr_cl_out                          false
% 19.56/2.98  
% 19.56/2.98  ------ Global Options
% 19.56/2.98  
% 19.56/2.98  --schedule                              default
% 19.56/2.98  --add_important_lit                     false
% 19.56/2.98  --prop_solver_per_cl                    1000
% 19.56/2.98  --min_unsat_core                        false
% 19.56/2.98  --soft_assumptions                      false
% 19.56/2.98  --soft_lemma_size                       3
% 19.56/2.98  --prop_impl_unit_size                   0
% 19.56/2.98  --prop_impl_unit                        []
% 19.56/2.98  --share_sel_clauses                     true
% 19.56/2.98  --reset_solvers                         false
% 19.56/2.98  --bc_imp_inh                            [conj_cone]
% 19.56/2.98  --conj_cone_tolerance                   3.
% 19.56/2.98  --extra_neg_conj                        none
% 19.56/2.98  --large_theory_mode                     true
% 19.56/2.98  --prolific_symb_bound                   200
% 19.56/2.98  --lt_threshold                          2000
% 19.56/2.98  --clause_weak_htbl                      true
% 19.56/2.98  --gc_record_bc_elim                     false
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing Options
% 19.56/2.98  
% 19.56/2.98  --preprocessing_flag                    true
% 19.56/2.98  --time_out_prep_mult                    0.1
% 19.56/2.98  --splitting_mode                        input
% 19.56/2.98  --splitting_grd                         true
% 19.56/2.98  --splitting_cvd                         false
% 19.56/2.98  --splitting_cvd_svl                     false
% 19.56/2.98  --splitting_nvd                         32
% 19.56/2.98  --sub_typing                            true
% 19.56/2.98  --prep_gs_sim                           true
% 19.56/2.98  --prep_unflatten                        true
% 19.56/2.98  --prep_res_sim                          true
% 19.56/2.98  --prep_upred                            true
% 19.56/2.98  --prep_sem_filter                       exhaustive
% 19.56/2.98  --prep_sem_filter_out                   false
% 19.56/2.98  --pred_elim                             true
% 19.56/2.98  --res_sim_input                         true
% 19.56/2.98  --eq_ax_congr_red                       true
% 19.56/2.98  --pure_diseq_elim                       true
% 19.56/2.98  --brand_transform                       false
% 19.56/2.98  --non_eq_to_eq                          false
% 19.56/2.98  --prep_def_merge                        true
% 19.56/2.98  --prep_def_merge_prop_impl              false
% 19.56/2.98  --prep_def_merge_mbd                    true
% 19.56/2.98  --prep_def_merge_tr_red                 false
% 19.56/2.98  --prep_def_merge_tr_cl                  false
% 19.56/2.98  --smt_preprocessing                     true
% 19.56/2.98  --smt_ac_axioms                         fast
% 19.56/2.98  --preprocessed_out                      false
% 19.56/2.98  --preprocessed_stats                    false
% 19.56/2.98  
% 19.56/2.98  ------ Abstraction refinement Options
% 19.56/2.98  
% 19.56/2.98  --abstr_ref                             []
% 19.56/2.98  --abstr_ref_prep                        false
% 19.56/2.98  --abstr_ref_until_sat                   false
% 19.56/2.98  --abstr_ref_sig_restrict                funpre
% 19.56/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.56/2.98  --abstr_ref_under                       []
% 19.56/2.98  
% 19.56/2.98  ------ SAT Options
% 19.56/2.98  
% 19.56/2.98  --sat_mode                              false
% 19.56/2.98  --sat_fm_restart_options                ""
% 19.56/2.98  --sat_gr_def                            false
% 19.56/2.98  --sat_epr_types                         true
% 19.56/2.98  --sat_non_cyclic_types                  false
% 19.56/2.98  --sat_finite_models                     false
% 19.56/2.98  --sat_fm_lemmas                         false
% 19.56/2.98  --sat_fm_prep                           false
% 19.56/2.98  --sat_fm_uc_incr                        true
% 19.56/2.98  --sat_out_model                         small
% 19.56/2.98  --sat_out_clauses                       false
% 19.56/2.98  
% 19.56/2.98  ------ QBF Options
% 19.56/2.98  
% 19.56/2.98  --qbf_mode                              false
% 19.56/2.98  --qbf_elim_univ                         false
% 19.56/2.98  --qbf_dom_inst                          none
% 19.56/2.98  --qbf_dom_pre_inst                      false
% 19.56/2.98  --qbf_sk_in                             false
% 19.56/2.98  --qbf_pred_elim                         true
% 19.56/2.98  --qbf_split                             512
% 19.56/2.98  
% 19.56/2.98  ------ BMC1 Options
% 19.56/2.98  
% 19.56/2.98  --bmc1_incremental                      false
% 19.56/2.98  --bmc1_axioms                           reachable_all
% 19.56/2.98  --bmc1_min_bound                        0
% 19.56/2.98  --bmc1_max_bound                        -1
% 19.56/2.98  --bmc1_max_bound_default                -1
% 19.56/2.98  --bmc1_symbol_reachability              true
% 19.56/2.98  --bmc1_property_lemmas                  false
% 19.56/2.98  --bmc1_k_induction                      false
% 19.56/2.98  --bmc1_non_equiv_states                 false
% 19.56/2.98  --bmc1_deadlock                         false
% 19.56/2.98  --bmc1_ucm                              false
% 19.56/2.98  --bmc1_add_unsat_core                   none
% 19.56/2.98  --bmc1_unsat_core_children              false
% 19.56/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.56/2.98  --bmc1_out_stat                         full
% 19.56/2.98  --bmc1_ground_init                      false
% 19.56/2.98  --bmc1_pre_inst_next_state              false
% 19.56/2.98  --bmc1_pre_inst_state                   false
% 19.56/2.98  --bmc1_pre_inst_reach_state             false
% 19.56/2.98  --bmc1_out_unsat_core                   false
% 19.56/2.98  --bmc1_aig_witness_out                  false
% 19.56/2.98  --bmc1_verbose                          false
% 19.56/2.98  --bmc1_dump_clauses_tptp                false
% 19.56/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.56/2.98  --bmc1_dump_file                        -
% 19.56/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.56/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.56/2.98  --bmc1_ucm_extend_mode                  1
% 19.56/2.98  --bmc1_ucm_init_mode                    2
% 19.56/2.98  --bmc1_ucm_cone_mode                    none
% 19.56/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.56/2.98  --bmc1_ucm_relax_model                  4
% 19.56/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.56/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.56/2.98  --bmc1_ucm_layered_model                none
% 19.56/2.98  --bmc1_ucm_max_lemma_size               10
% 19.56/2.98  
% 19.56/2.98  ------ AIG Options
% 19.56/2.98  
% 19.56/2.98  --aig_mode                              false
% 19.56/2.98  
% 19.56/2.98  ------ Instantiation Options
% 19.56/2.98  
% 19.56/2.98  --instantiation_flag                    true
% 19.56/2.98  --inst_sos_flag                         true
% 19.56/2.98  --inst_sos_phase                        true
% 19.56/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.56/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.56/2.98  --inst_lit_sel_side                     none
% 19.56/2.98  --inst_solver_per_active                1400
% 19.56/2.98  --inst_solver_calls_frac                1.
% 19.56/2.98  --inst_passive_queue_type               priority_queues
% 19.56/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.56/2.98  --inst_passive_queues_freq              [25;2]
% 19.56/2.98  --inst_dismatching                      true
% 19.56/2.98  --inst_eager_unprocessed_to_passive     true
% 19.56/2.98  --inst_prop_sim_given                   true
% 19.56/2.98  --inst_prop_sim_new                     false
% 19.56/2.98  --inst_subs_new                         false
% 19.56/2.98  --inst_eq_res_simp                      false
% 19.56/2.98  --inst_subs_given                       false
% 19.56/2.98  --inst_orphan_elimination               true
% 19.56/2.98  --inst_learning_loop_flag               true
% 19.56/2.98  --inst_learning_start                   3000
% 19.56/2.98  --inst_learning_factor                  2
% 19.56/2.98  --inst_start_prop_sim_after_learn       3
% 19.56/2.98  --inst_sel_renew                        solver
% 19.56/2.98  --inst_lit_activity_flag                true
% 19.56/2.98  --inst_restr_to_given                   false
% 19.56/2.98  --inst_activity_threshold               500
% 19.56/2.98  --inst_out_proof                        true
% 19.56/2.98  
% 19.56/2.98  ------ Resolution Options
% 19.56/2.98  
% 19.56/2.98  --resolution_flag                       false
% 19.56/2.98  --res_lit_sel                           adaptive
% 19.56/2.98  --res_lit_sel_side                      none
% 19.56/2.98  --res_ordering                          kbo
% 19.56/2.98  --res_to_prop_solver                    active
% 19.56/2.98  --res_prop_simpl_new                    false
% 19.56/2.98  --res_prop_simpl_given                  true
% 19.56/2.98  --res_passive_queue_type                priority_queues
% 19.56/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.56/2.98  --res_passive_queues_freq               [15;5]
% 19.56/2.98  --res_forward_subs                      full
% 19.56/2.98  --res_backward_subs                     full
% 19.56/2.98  --res_forward_subs_resolution           true
% 19.56/2.98  --res_backward_subs_resolution          true
% 19.56/2.98  --res_orphan_elimination                true
% 19.56/2.98  --res_time_limit                        2.
% 19.56/2.98  --res_out_proof                         true
% 19.56/2.98  
% 19.56/2.98  ------ Superposition Options
% 19.56/2.98  
% 19.56/2.98  --superposition_flag                    true
% 19.56/2.98  --sup_passive_queue_type                priority_queues
% 19.56/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.56/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.56/2.98  --demod_completeness_check              fast
% 19.56/2.98  --demod_use_ground                      true
% 19.56/2.98  --sup_to_prop_solver                    passive
% 19.56/2.98  --sup_prop_simpl_new                    true
% 19.56/2.98  --sup_prop_simpl_given                  true
% 19.56/2.98  --sup_fun_splitting                     true
% 19.56/2.98  --sup_smt_interval                      50000
% 19.56/2.98  
% 19.56/2.98  ------ Superposition Simplification Setup
% 19.56/2.98  
% 19.56/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.56/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.56/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.56/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.56/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.56/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.56/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.56/2.98  --sup_immed_triv                        [TrivRules]
% 19.56/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_immed_bw_main                     []
% 19.56/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.56/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.56/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/2.98  --sup_input_bw                          []
% 19.56/2.98  
% 19.56/2.98  ------ Combination Options
% 19.56/2.98  
% 19.56/2.98  --comb_res_mult                         3
% 19.56/2.98  --comb_sup_mult                         2
% 19.56/2.98  --comb_inst_mult                        10
% 19.56/2.98  
% 19.56/2.98  ------ Debug Options
% 19.56/2.98  
% 19.56/2.98  --dbg_backtrace                         false
% 19.56/2.98  --dbg_dump_prop_clauses                 false
% 19.56/2.98  --dbg_dump_prop_clauses_file            -
% 19.56/2.98  --dbg_out_stat                          false
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  ------ Proving...
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  % SZS status Theorem for theBenchmark.p
% 19.56/2.98  
% 19.56/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.56/2.98  
% 19.56/2.98  fof(f18,conjecture,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f19,negated_conjecture,(
% 19.56/2.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 19.56/2.98    inference(negated_conjecture,[],[f18])).
% 19.56/2.98  
% 19.56/2.98  fof(f35,plain,(
% 19.56/2.98    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f19])).
% 19.56/2.98  
% 19.56/2.98  fof(f36,plain,(
% 19.56/2.98    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f35])).
% 19.56/2.98  
% 19.56/2.98  fof(f59,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK9) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK9,X0,k1_tarski(X1)) & v1_funct_1(sK9))) )),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f58,plain,(
% 19.56/2.98    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK6,k1_tarski(sK7),sK8) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(X3,sK6,k1_tarski(sK7)) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_1(sK8))),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f60,plain,(
% 19.56/2.98    (k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_1(sK8)),
% 19.56/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f36,f59,f58])).
% 19.56/2.98  
% 19.56/2.98  fof(f109,plain,(
% 19.56/2.98    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f4,axiom,(
% 19.56/2.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f66,plain,(
% 19.56/2.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f4])).
% 19.56/2.98  
% 19.56/2.98  fof(f5,axiom,(
% 19.56/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f67,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f5])).
% 19.56/2.98  
% 19.56/2.98  fof(f6,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f68,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f6])).
% 19.56/2.98  
% 19.56/2.98  fof(f111,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f67,f68])).
% 19.56/2.98  
% 19.56/2.98  fof(f112,plain,(
% 19.56/2.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f66,f111])).
% 19.56/2.98  
% 19.56/2.98  fof(f123,plain,(
% 19.56/2.98    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))),
% 19.56/2.98    inference(definition_unfolding,[],[f109,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f14,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f27,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f14])).
% 19.56/2.98  
% 19.56/2.98  fof(f28,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f27])).
% 19.56/2.98  
% 19.56/2.98  fof(f98,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f28])).
% 19.56/2.98  
% 19.56/2.98  fof(f107,plain,(
% 19.56/2.98    v1_funct_1(sK9)),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f108,plain,(
% 19.56/2.98    v1_funct_2(sK9,sK6,k1_tarski(sK7))),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f124,plain,(
% 19.56/2.98    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))),
% 19.56/2.98    inference(definition_unfolding,[],[f108,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f7,axiom,(
% 19.56/2.98    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f21,plain,(
% 19.56/2.98    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 19.56/2.98    inference(ennf_transformation,[],[f7])).
% 19.56/2.98  
% 19.56/2.98  fof(f42,plain,(
% 19.56/2.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f43,plain,(
% 19.56/2.98    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 19.56/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f42])).
% 19.56/2.98  
% 19.56/2.98  fof(f69,plain,(
% 19.56/2.98    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 19.56/2.98    inference(cnf_transformation,[],[f43])).
% 19.56/2.98  
% 19.56/2.98  fof(f114,plain,(
% 19.56/2.98    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 19.56/2.98    inference(definition_unfolding,[],[f69,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f16,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f31,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f16])).
% 19.56/2.98  
% 19.56/2.98  fof(f32,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f31])).
% 19.56/2.98  
% 19.56/2.98  fof(f103,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f32])).
% 19.56/2.98  
% 19.56/2.98  fof(f12,axiom,(
% 19.56/2.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f23,plain,(
% 19.56/2.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.56/2.98    inference(ennf_transformation,[],[f12])).
% 19.56/2.98  
% 19.56/2.98  fof(f24,plain,(
% 19.56/2.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/2.98    inference(flattening,[],[f23])).
% 19.56/2.98  
% 19.56/2.98  fof(f49,plain,(
% 19.56/2.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/2.98    inference(nnf_transformation,[],[f24])).
% 19.56/2.98  
% 19.56/2.98  fof(f81,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.56/2.98    inference(cnf_transformation,[],[f49])).
% 19.56/2.98  
% 19.56/2.98  fof(f17,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f33,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f17])).
% 19.56/2.98  
% 19.56/2.98  fof(f34,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f33])).
% 19.56/2.98  
% 19.56/2.98  fof(f104,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f34])).
% 19.56/2.98  
% 19.56/2.98  fof(f121,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f104,f112,f112,f112,f112,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f101,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f32])).
% 19.56/2.98  
% 19.56/2.98  fof(f102,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f32])).
% 19.56/2.98  
% 19.56/2.98  fof(f70,plain,(
% 19.56/2.98    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 19.56/2.98    inference(cnf_transformation,[],[f43])).
% 19.56/2.98  
% 19.56/2.98  fof(f113,plain,(
% 19.56/2.98    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 19.56/2.98    inference(definition_unfolding,[],[f70,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f106,plain,(
% 19.56/2.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f125,plain,(
% 19.56/2.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))),
% 19.56/2.98    inference(definition_unfolding,[],[f106,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f105,plain,(
% 19.56/2.98    v1_funct_1(sK8)),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f110,plain,(
% 19.56/2.98    k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8)),
% 19.56/2.98    inference(cnf_transformation,[],[f60])).
% 19.56/2.98  
% 19.56/2.98  fof(f122,plain,(
% 19.56/2.98    k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)),
% 19.56/2.98    inference(definition_unfolding,[],[f110,f112,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f13,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f25,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f13])).
% 19.56/2.98  
% 19.56/2.98  fof(f26,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f25])).
% 19.56/2.98  
% 19.56/2.98  fof(f38,plain,(
% 19.56/2.98    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 19.56/2.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 19.56/2.98  
% 19.56/2.98  fof(f37,plain,(
% 19.56/2.98    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 19.56/2.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 19.56/2.98  
% 19.56/2.98  fof(f39,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(definition_folding,[],[f26,f38,f37])).
% 19.56/2.98  
% 19.56/2.98  fof(f97,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f39])).
% 19.56/2.98  
% 19.56/2.98  fof(f50,plain,(
% 19.56/2.98    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 19.56/2.98    inference(nnf_transformation,[],[f38])).
% 19.56/2.98  
% 19.56/2.98  fof(f51,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 19.56/2.98    inference(rectify,[],[f50])).
% 19.56/2.98  
% 19.56/2.98  fof(f83,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f51])).
% 19.56/2.98  
% 19.56/2.98  fof(f131,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 19.56/2.98    inference(equality_resolution,[],[f83])).
% 19.56/2.98  
% 19.56/2.98  fof(f52,plain,(
% 19.56/2.98    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 19.56/2.98    inference(nnf_transformation,[],[f37])).
% 19.56/2.98  
% 19.56/2.98  fof(f53,plain,(
% 19.56/2.98    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 19.56/2.98    inference(rectify,[],[f52])).
% 19.56/2.98  
% 19.56/2.98  fof(f56,plain,(
% 19.56/2.98    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f55,plain,(
% 19.56/2.98    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f54,plain,(
% 19.56/2.98    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 19.56/2.98    introduced(choice_axiom,[])).
% 19.56/2.98  
% 19.56/2.98  fof(f57,plain,(
% 19.56/2.98    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 19.56/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f53,f56,f55,f54])).
% 19.56/2.98  
% 19.56/2.98  fof(f90,plain,(
% 19.56/2.98    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f57])).
% 19.56/2.98  
% 19.56/2.98  fof(f133,plain,(
% 19.56/2.98    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 19.56/2.98    inference(equality_resolution,[],[f90])).
% 19.56/2.98  
% 19.56/2.98  fof(f15,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f29,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 19.56/2.98    inference(ennf_transformation,[],[f15])).
% 19.56/2.98  
% 19.56/2.98  fof(f30,plain,(
% 19.56/2.98    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 19.56/2.98    inference(flattening,[],[f29])).
% 19.56/2.98  
% 19.56/2.98  fof(f100,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f30])).
% 19.56/2.98  
% 19.56/2.98  fof(f120,plain,(
% 19.56/2.98    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f100,f112,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f8,axiom,(
% 19.56/2.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f44,plain,(
% 19.56/2.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.56/2.98    inference(nnf_transformation,[],[f8])).
% 19.56/2.98  
% 19.56/2.98  fof(f45,plain,(
% 19.56/2.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.56/2.98    inference(flattening,[],[f44])).
% 19.56/2.98  
% 19.56/2.98  fof(f71,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f45])).
% 19.56/2.98  
% 19.56/2.98  fof(f72,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.56/2.98    inference(cnf_transformation,[],[f45])).
% 19.56/2.98  
% 19.56/2.98  fof(f129,plain,(
% 19.56/2.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.56/2.98    inference(equality_resolution,[],[f72])).
% 19.56/2.98  
% 19.56/2.98  fof(f10,axiom,(
% 19.56/2.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f46,plain,(
% 19.56/2.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.56/2.98    inference(nnf_transformation,[],[f10])).
% 19.56/2.98  
% 19.56/2.98  fof(f47,plain,(
% 19.56/2.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.56/2.98    inference(flattening,[],[f46])).
% 19.56/2.98  
% 19.56/2.98  fof(f78,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f47])).
% 19.56/2.98  
% 19.56/2.98  fof(f117,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f78,f111])).
% 19.56/2.98  
% 19.56/2.98  fof(f3,axiom,(
% 19.56/2.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f20,plain,(
% 19.56/2.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 19.56/2.98    inference(ennf_transformation,[],[f3])).
% 19.56/2.98  
% 19.56/2.98  fof(f65,plain,(
% 19.56/2.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f20])).
% 19.56/2.98  
% 19.56/2.98  fof(f77,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f47])).
% 19.56/2.98  
% 19.56/2.98  fof(f118,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f77,f111])).
% 19.56/2.98  
% 19.56/2.98  fof(f1,axiom,(
% 19.56/2.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f40,plain,(
% 19.56/2.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.56/2.98    inference(nnf_transformation,[],[f1])).
% 19.56/2.98  
% 19.56/2.98  fof(f41,plain,(
% 19.56/2.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.56/2.98    inference(flattening,[],[f40])).
% 19.56/2.98  
% 19.56/2.98  fof(f62,plain,(
% 19.56/2.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.56/2.98    inference(cnf_transformation,[],[f41])).
% 19.56/2.98  
% 19.56/2.98  fof(f126,plain,(
% 19.56/2.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.56/2.98    inference(equality_resolution,[],[f62])).
% 19.56/2.98  
% 19.56/2.98  fof(f76,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f47])).
% 19.56/2.98  
% 19.56/2.98  fof(f119,plain,(
% 19.56/2.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 19.56/2.98    inference(definition_unfolding,[],[f76,f111])).
% 19.56/2.98  
% 19.56/2.98  fof(f87,plain,(
% 19.56/2.98    ( ! [X2,X0,X7,X3,X1] : (sK5(X0,X1,X2,X7) = X7 | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f57])).
% 19.56/2.98  
% 19.56/2.98  fof(f88,plain,(
% 19.56/2.98    ( ! [X2,X0,X7,X3,X1] : (v1_partfun1(sK5(X0,X1,X2,X7),X1) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f57])).
% 19.56/2.98  
% 19.56/2.98  fof(f9,axiom,(
% 19.56/2.98    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f22,plain,(
% 19.56/2.98    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 19.56/2.98    inference(ennf_transformation,[],[f9])).
% 19.56/2.98  
% 19.56/2.98  fof(f74,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 19.56/2.98    inference(cnf_transformation,[],[f22])).
% 19.56/2.98  
% 19.56/2.98  fof(f116,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 19.56/2.98    inference(definition_unfolding,[],[f74,f112])).
% 19.56/2.98  
% 19.56/2.98  fof(f73,plain,(
% 19.56/2.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.56/2.98    inference(cnf_transformation,[],[f45])).
% 19.56/2.98  
% 19.56/2.98  fof(f128,plain,(
% 19.56/2.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.56/2.98    inference(equality_resolution,[],[f73])).
% 19.56/2.98  
% 19.56/2.98  fof(f2,axiom,(
% 19.56/2.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f64,plain,(
% 19.56/2.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f2])).
% 19.56/2.98  
% 19.56/2.98  fof(f11,axiom,(
% 19.56/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.56/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.98  
% 19.56/2.98  fof(f48,plain,(
% 19.56/2.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.56/2.98    inference(nnf_transformation,[],[f11])).
% 19.56/2.98  
% 19.56/2.98  fof(f79,plain,(
% 19.56/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.56/2.98    inference(cnf_transformation,[],[f48])).
% 19.56/2.98  
% 19.56/2.98  fof(f63,plain,(
% 19.56/2.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.56/2.98    inference(cnf_transformation,[],[f41])).
% 19.56/2.98  
% 19.56/2.98  cnf(c_42,negated_conjecture,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 19.56/2.98      inference(cnf_transformation,[],[f123]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5093,plain,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_35,plain,
% 19.56/2.98      ( ~ v1_funct_2(X0,X1,X2)
% 19.56/2.98      | v1_partfun1(X0,X1)
% 19.56/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | ~ v1_funct_1(X0)
% 19.56/2.98      | k1_xboole_0 = X2 ),
% 19.56/2.98      inference(cnf_transformation,[],[f98]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5098,plain,
% 19.56/2.98      ( k1_xboole_0 = X0
% 19.56/2.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 19.56/2.98      | v1_partfun1(X1,X2) = iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_10818,plain,
% 19.56/2.98      ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
% 19.56/2.98      | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) = iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5098]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_44,negated_conjecture,
% 19.56/2.98      ( v1_funct_1(sK9) ),
% 19.56/2.98      inference(cnf_transformation,[],[f107]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_49,plain,
% 19.56/2.98      ( v1_funct_1(sK9) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_43,negated_conjecture,
% 19.56/2.98      ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 19.56/2.98      inference(cnf_transformation,[],[f124]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_50,plain,
% 19.56/2.98      ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_11397,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) = iProver_top
% 19.56/2.98      | k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_10818,c_49,c_50]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_11398,plain,
% 19.56/2.98      ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
% 19.56/2.98      | v1_partfun1(sK9,sK6) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_11397]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_6,plain,
% 19.56/2.98      ( r2_hidden(sK2(X0,X1),X0)
% 19.56/2.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 19.56/2.98      | k1_xboole_0 = X0 ),
% 19.56/2.98      inference(cnf_transformation,[],[f114]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5117,plain,
% 19.56/2.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 19.56/2.98      | k1_xboole_0 = X1
% 19.56/2.98      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_37,plain,
% 19.56/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 19.56/2.98      | ~ v1_funct_1(X0) ),
% 19.56/2.98      inference(cnf_transformation,[],[f103]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5096,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.56/2.98      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9226,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5096]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9584,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_9226,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9585,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_9584]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9594,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_9585]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_18,plain,
% 19.56/2.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.56/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.56/2.98      | X3 = X2 ),
% 19.56/2.98      inference(cnf_transformation,[],[f81]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_40,plain,
% 19.56/2.98      ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
% 19.56/2.98      | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
% 19.56/2.98      | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 19.56/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 19.56/2.98      | ~ v1_funct_1(X2)
% 19.56/2.98      | ~ v1_funct_1(X3) ),
% 19.56/2.98      inference(cnf_transformation,[],[f121]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_590,plain,
% 19.56/2.98      ( ~ v1_funct_2(X0,X1,k2_enumset1(X2,X2,X2,X2))
% 19.56/2.98      | ~ v1_funct_2(X3,X1,k2_enumset1(X2,X2,X2,X2))
% 19.56/2.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 19.56/2.98      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 19.56/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 19.56/2.98      | ~ v1_funct_1(X3)
% 19.56/2.98      | ~ v1_funct_1(X0)
% 19.56/2.98      | X3 != X7
% 19.56/2.98      | X0 != X4
% 19.56/2.98      | X1 != X5
% 19.56/2.98      | X4 = X7
% 19.56/2.98      | k2_enumset1(X2,X2,X2,X2) != X6 ),
% 19.56/2.98      inference(resolution_lifted,[status(thm)],[c_18,c_40]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_591,plain,
% 19.56/2.98      ( ~ v1_funct_2(X0,X1,k2_enumset1(X2,X2,X2,X2))
% 19.56/2.98      | ~ v1_funct_2(X3,X1,k2_enumset1(X2,X2,X2,X2))
% 19.56/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 19.56/2.98      | ~ v1_funct_1(X0)
% 19.56/2.98      | ~ v1_funct_1(X3)
% 19.56/2.98      | X0 = X3 ),
% 19.56/2.98      inference(unflattening,[status(thm)],[c_590]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5086,plain,
% 19.56/2.98      ( X0 = X1
% 19.56/2.98      | v1_funct_2(X0,X2,k2_enumset1(X3,X3,X3,X3)) != iProver_top
% 19.56/2.98      | v1_funct_2(X1,X2,k2_enumset1(X3,X3,X3,X3)) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9698,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top
% 19.56/2.98      | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0)) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_9594,c_5086]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_39,plain,
% 19.56/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 19.56/2.98      | ~ v1_funct_1(X0)
% 19.56/2.98      | v1_funct_1(X3) ),
% 19.56/2.98      inference(cnf_transformation,[],[f101]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5094,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top
% 19.56/2.98      | v1_funct_1(X3) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7678,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) = iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5094]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7984,plain,
% 19.56/2.98      ( v1_funct_1(X0) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_7678,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7985,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_7984]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7991,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_7985]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_38,plain,
% 19.56/2.98      ( v1_funct_2(X0,X1,X2)
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 19.56/2.98      | ~ v1_funct_1(X3) ),
% 19.56/2.98      inference(cnf_transformation,[],[f102]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5095,plain,
% 19.56/2.98      ( v1_funct_2(X0,X1,X2) = iProver_top
% 19.56/2.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
% 19.56/2.98      | v1_funct_1(X3) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8442,plain,
% 19.56/2.98      ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5095]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8676,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_8442,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8677,plain,
% 19.56/2.98      ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_8676]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8685,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_8677]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_45494,plain,
% 19.56/2.98      ( v1_funct_1(X1) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_9698,c_7991,c_8685]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_45495,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_45494]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_45502,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
% 19.56/2.98      | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_45495]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_45545,plain,
% 19.56/2.98      ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 19.56/2.98      | ~ v1_funct_1(sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
% 19.56/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_45502]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_46389,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_45502,c_49,c_50]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5,plain,
% 19.56/2.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 19.56/2.98      | sK2(X1,X0) != X0
% 19.56/2.98      | k1_xboole_0 = X1 ),
% 19.56/2.98      inference(cnf_transformation,[],[f113]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_46398,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK9 != X0 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_46389,c_5]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_47012,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0 ),
% 19.56/2.98      inference(equality_resolution,[status(thm)],[c_46398]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_47656,plain,
% 19.56/2.98      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_47012,c_46389]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_45,negated_conjecture,
% 19.56/2.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 19.56/2.98      inference(cnf_transformation,[],[f125]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5090,plain,
% 19.56/2.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9227,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_5096]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_46,negated_conjecture,
% 19.56/2.98      ( v1_funct_1(sK8) ),
% 19.56/2.98      inference(cnf_transformation,[],[f105]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_47,plain,
% 19.56/2.98      ( v1_funct_1(sK8) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9611,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_9227,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9612,plain,
% 19.56/2.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_9611]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9621,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_9612]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9731,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top
% 19.56/2.98      | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0)) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_9621,c_5086]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7679,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) = iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_5094]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7999,plain,
% 19.56/2.98      ( v1_funct_1(X0) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_7679,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8000,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_7999]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8006,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_8000]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8443,plain,
% 19.56/2.98      ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_5095]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8815,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top
% 19.56/2.98      | v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_8443,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8816,plain,
% 19.56/2.98      ( v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_8815]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8824,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0),sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5117,c_8816]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_59665,plain,
% 19.56/2.98      ( v1_funct_1(X1) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_9731,c_8006,c_8824]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_59666,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = X1
% 19.56/2.98      | v1_funct_2(X1,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_59665]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_59673,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9
% 19.56/2.98      | v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_59666]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_59719,plain,
% 19.56/2.98      ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 19.56/2.98      | ~ v1_funct_1(sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
% 19.56/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_59673]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_60484,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_59673,c_49,c_50]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_41,negated_conjecture,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 19.56/2.98      inference(cnf_transformation,[],[f122]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_60638,plain,
% 19.56/2.98      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_60484,c_41]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61059,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),X0) = sK9
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_47656,c_60638]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_4245,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5169,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != X0
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4245]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5192,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5169]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_4244,plain,( X0 = X0 ),theory(equality) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5246,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4244]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61064,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) = sK9 ),
% 19.56/2.98      inference(equality_resolution,[status(thm)],[c_60638]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61197,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_61064,c_5]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61215,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_61059,c_41,c_5192,c_5246,c_61197]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_33,plain,
% 19.56/2.98      ( sP1(X0,X1,X2)
% 19.56/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 19.56/2.98      | ~ v1_funct_1(X2) ),
% 19.56/2.98      inference(cnf_transformation,[],[f97]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_20,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 19.56/2.98      inference(cnf_transformation,[],[f131]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_546,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 19.56/2.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 19.56/2.98      | ~ v1_funct_1(X3)
% 19.56/2.98      | X1 != X4
% 19.56/2.98      | X2 != X5
% 19.56/2.98      | X0 != X3 ),
% 19.56/2.98      inference(resolution_lifted,[status(thm)],[c_33,c_20]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_547,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 19.56/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | ~ v1_funct_1(X0) ),
% 19.56/2.98      inference(unflattening,[status(thm)],[c_546]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5088,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_27,plain,
% 19.56/2.98      ( ~ sP0(X0,X1,X2,X3)
% 19.56/2.98      | ~ v1_partfun1(X4,X1)
% 19.56/2.98      | ~ r1_partfun1(X0,X4)
% 19.56/2.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/2.98      | r2_hidden(X4,X3)
% 19.56/2.98      | ~ v1_funct_1(X4) ),
% 19.56/2.98      inference(cnf_transformation,[],[f133]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5105,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,X3) != iProver_top
% 19.56/2.98      | v1_partfun1(X4,X1) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,X4) != iProver_top
% 19.56/2.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | r2_hidden(X4,X3) = iProver_top
% 19.56/2.98      | v1_funct_1(X4) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12070,plain,
% 19.56/2.98      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK9) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,X1) = iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5105]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12362,plain,
% 19.56/2.98      ( r2_hidden(sK9,X1) = iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK9) != iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12070,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12363,plain,
% 19.56/2.98      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK9) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,X1) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_12362]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12368,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK9) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5088,c_12363]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_36,plain,
% 19.56/2.98      ( r1_partfun1(X0,X1)
% 19.56/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 19.56/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 19.56/2.98      | ~ v1_funct_1(X0)
% 19.56/2.98      | ~ v1_funct_1(X1) ),
% 19.56/2.98      inference(cnf_transformation,[],[f120]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5097,plain,
% 19.56/2.98      ( r1_partfun1(X0,X1) = iProver_top
% 19.56/2.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top
% 19.56/2.98      | v1_funct_1(X1) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_10031,plain,
% 19.56/2.98      ( r1_partfun1(X0,sK9) = iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_5097]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12493,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12368,c_49,c_10031]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12502,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_12493]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12720,plain,
% 19.56/2.98      ( r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12502,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12721,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_12720]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61322,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 19.56/2.98      inference(demodulation,[status(thm)],[c_61215,c_12721]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9,plain,
% 19.56/2.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 19.56/2.98      | k1_xboole_0 = X0
% 19.56/2.98      | k1_xboole_0 = X1 ),
% 19.56/2.98      inference(cnf_transformation,[],[f71]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_135,plain,
% 19.56/2.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.56/2.98      | k1_xboole_0 = k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_9]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8,plain,
% 19.56/2.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.56/2.98      inference(cnf_transformation,[],[f129]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_136,plain,
% 19.56/2.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_8]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5193,plain,
% 19.56/2.98      ( X0 != X1
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) != X1
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4245]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5283,plain,
% 19.56/2.98      ( X0 != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = X0
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5193]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5284,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = k1_xboole_0
% 19.56/2.98      | k1_xboole_0 != k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5283]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5353,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != X0
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X0
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4245]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5354,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k1_xboole_0
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5353]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12,plain,
% 19.56/2.98      ( ~ r2_hidden(X0,X1)
% 19.56/2.98      | ~ r2_hidden(X2,X1)
% 19.56/2.98      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 19.56/2.98      inference(cnf_transformation,[],[f117]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5363,plain,
% 19.56/2.98      ( ~ r2_hidden(sK9,k1_xboole_0)
% 19.56/2.98      | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_12]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5364,plain,
% 19.56/2.98      ( r2_hidden(sK9,k1_xboole_0) != iProver_top
% 19.56/2.98      | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_5363]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_4,plain,
% 19.56/2.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 19.56/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5770,plain,
% 19.56/2.98      ( ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0)
% 19.56/2.98      | k1_xboole_0 = k2_enumset1(sK9,sK9,sK9,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5771,plain,
% 19.56/2.98      ( k1_xboole_0 = k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k1_xboole_0) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_5770]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5887,plain,
% 19.56/2.98      ( sK9 = sK9 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4244]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12501,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_12493]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12712,plain,
% 19.56/2.98      ( r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top
% 19.56/2.98      | v1_partfun1(sK9,sK6) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12501,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12713,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_12712]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_4248,plain,
% 19.56/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.56/2.98      theory(equality) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5812,plain,
% 19.56/2.98      ( ~ r2_hidden(X0,X1)
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0)
% 19.56/2.98      | sK9 != X0
% 19.56/2.98      | k1_xboole_0 != X1 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4248]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7084,plain,
% 19.56/2.98      ( ~ r2_hidden(sK9,X0)
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0)
% 19.56/2.98      | sK9 != sK9
% 19.56/2.98      | k1_xboole_0 != X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5812]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_34277,plain,
% 19.56/2.98      ( ~ r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9))
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0)
% 19.56/2.98      | sK9 != sK9
% 19.56/2.98      | k1_xboole_0 != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_7084]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_34284,plain,
% 19.56/2.98      ( sK9 != sK9
% 19.56/2.98      | k1_xboole_0 != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_34277]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_37002,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != X0
% 19.56/2.98      | k1_xboole_0 != X0
% 19.56/2.98      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4245]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_37003,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k1_xboole_0
% 19.56/2.98      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)
% 19.56/2.98      | k1_xboole_0 != k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_37002]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12071,plain,
% 19.56/2.98      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 19.56/2.98      | v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK8) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,X1) = iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_5105]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12482,plain,
% 19.56/2.98      ( r2_hidden(sK8,X1) = iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK8) != iProver_top
% 19.56/2.98      | v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12071,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12483,plain,
% 19.56/2.98      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 19.56/2.98      | v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK8) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,X1) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_12482]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12488,plain,
% 19.56/2.98      ( v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r1_partfun1(X0,sK8) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5088,c_12483]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_10032,plain,
% 19.56/2.98      ( r1_partfun1(X0,sK8) = iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_5097]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12808,plain,
% 19.56/2.98      ( v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0)) = iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12488,c_47,c_10032]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12817,plain,
% 19.56/2.98      ( v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
% 19.56/2.98      | v1_funct_1(sK8) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5090,c_12808]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12970,plain,
% 19.56/2.98      ( r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top
% 19.56/2.98      | v1_partfun1(sK8,sK6) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_12817,c_47]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_12971,plain,
% 19.56/2.98      ( v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK8,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_12970]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5116,plain,
% 19.56/2.98      ( r2_hidden(X0,X1) != iProver_top
% 19.56/2.98      | r2_hidden(X2,X1) != iProver_top
% 19.56/2.98      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_13,plain,
% 19.56/2.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 19.56/2.98      inference(cnf_transformation,[],[f118]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5115,plain,
% 19.56/2.98      ( r2_hidden(X0,X1) = iProver_top
% 19.56/2.98      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_50171,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
% 19.56/2.98      | r2_hidden(sK9,X1) = iProver_top
% 19.56/2.98      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_47656,c_5115]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_56459,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),X0) = sK9
% 19.56/2.98      | r2_hidden(X0,X1) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,X1) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5116,c_50171]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_56498,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9),sK8) = sK9
% 19.56/2.98      | v1_partfun1(sK8,sK6) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_12971,c_56459]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_51,plain,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_46397,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k2_enumset1(X0,X0,X0,X0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_46389,c_5117]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_1,plain,
% 19.56/2.98      ( r1_tarski(X0,X0) ),
% 19.56/2.98      inference(cnf_transformation,[],[f126]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5818,plain,
% 19.56/2.98      ( r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_1]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5819,plain,
% 19.56/2.98      ( r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_5818]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_14,plain,
% 19.56/2.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X2),X1) ),
% 19.56/2.98      inference(cnf_transformation,[],[f119]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5864,plain,
% 19.56/2.98      ( r2_hidden(sK9,X0) | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,X1),X0) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_14]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7062,plain,
% 19.56/2.98      ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,X0))
% 19.56/2.98      | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,X0),k2_enumset1(sK9,sK9,sK9,X0)) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5864]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8409,plain,
% 19.56/2.98      ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
% 19.56/2.98      | ~ r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_7062]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_8410,plain,
% 19.56/2.98      ( r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9)) = iProver_top
% 19.56/2.98      | r1_tarski(k2_enumset1(sK9,sK9,sK9,sK9),k2_enumset1(sK9,sK9,sK9,sK9)) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_8409]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5872,plain,
% 19.56/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK9,X2) | X2 != X1 | sK9 != X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4248]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_9054,plain,
% 19.56/2.98      ( ~ r2_hidden(sK9,X0) | r2_hidden(sK9,X1) | X1 != X0 | sK9 != sK9 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5872]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_14786,plain,
% 19.56/2.98      ( r2_hidden(sK9,X0)
% 19.56/2.98      | ~ r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
% 19.56/2.98      | X0 != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | sK9 != sK9 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_9054]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_31359,plain,
% 19.56/2.98      ( ~ r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9))
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9))
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | sK9 != sK9 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_14786]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_31360,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) != k2_enumset1(sK9,sK9,sK9,sK9)
% 19.56/2.98      | sK9 != sK9
% 19.56/2.98      | r2_hidden(sK9,k2_enumset1(sK9,sK9,sK9,sK9)) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_31359]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_48312,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_46397,c_5819,c_5887,c_8410,c_31360,c_47012]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_30,plain,
% 19.56/2.98      ( ~ sP0(X0,X1,X2,X3) | ~ r2_hidden(X4,X3) | sK5(X0,X1,X2,X4) = X4 ),
% 19.56/2.98      inference(cnf_transformation,[],[f87]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5102,plain,
% 19.56/2.98      ( sK5(X0,X1,X2,X3) = X3
% 19.56/2.98      | sP0(X0,X1,X2,X4) != iProver_top
% 19.56/2.98      | r2_hidden(X3,X4) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7282,plain,
% 19.56/2.98      ( sK5(X0,X1,X2,X3) = X3
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5088,c_5102]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_17097,plain,
% 19.56/2.98      ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5093,c_7282]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_17586,plain,
% 19.56/2.98      ( r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0 ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_17097,c_49]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_17587,plain,
% 19.56/2.98      ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X0) = X0
% 19.56/2.98      | r2_hidden(X0,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top ),
% 19.56/2.98      inference(renaming,[status(thm)],[c_17586]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_48325,plain,
% 19.56/2.98      ( sK5(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK9
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_48312,c_17587]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_29,plain,
% 19.56/2.98      ( ~ sP0(X0,X1,X2,X3)
% 19.56/2.98      | v1_partfun1(sK5(X0,X1,X2,X4),X1)
% 19.56/2.98      | ~ r2_hidden(X4,X3) ),
% 19.56/2.98      inference(cnf_transformation,[],[f88]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5103,plain,
% 19.56/2.98      ( sP0(X0,X1,X2,X3) != iProver_top
% 19.56/2.98      | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top
% 19.56/2.98      | r2_hidden(X4,X3) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7804,plain,
% 19.56/2.98      ( v1_partfun1(sK5(X0,X1,X2,X3),X1) = iProver_top
% 19.56/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.56/2.98      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 19.56/2.98      | v1_funct_1(X0) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_5088,c_5103]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_48345,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | v1_partfun1(sK9,sK6) = iProver_top
% 19.56/2.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9)) != iProver_top
% 19.56/2.98      | v1_funct_1(sK9) != iProver_top ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_48325,c_7804]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_59410,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | r2_hidden(sK9,k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)) = iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_56498,c_47,c_49,c_51,c_12502,c_48312,c_48345]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_61220,plain,
% 19.56/2.98      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_xboole_0
% 19.56/2.98      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 19.56/2.98      inference(demodulation,[status(thm)],[c_61215,c_59410]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62354,plain,
% 19.56/2.98      ( v1_partfun1(sK9,sK6) != iProver_top ),
% 19.56/2.98      inference(global_propositional_subsumption,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_61322,c_49,c_41,c_135,c_136,c_5192,c_5246,c_5284,
% 19.56/2.98                 c_5354,c_5364,c_5771,c_5887,c_12501,c_34284,c_37003,
% 19.56/2.98                 c_61197,c_61220]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62358,plain,
% 19.56/2.98      ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_11398,c_62354]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_11,plain,
% 19.56/2.98      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
% 19.56/2.98      | k1_xboole_0 = X1 ),
% 19.56/2.98      inference(cnf_transformation,[],[f116]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62524,plain,
% 19.56/2.98      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 19.56/2.98      inference(superposition,[status(thm)],[c_62358,c_11]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62559,plain,
% 19.56/2.98      ( k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 19.56/2.98      inference(light_normalisation,[status(thm)],[c_62524,c_8]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62560,plain,
% 19.56/2.98      ( k1_xboole_0 = X0 ),
% 19.56/2.98      inference(equality_resolution_simp,[status(thm)],[c_62559]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62563,plain,
% 19.56/2.98      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.56/2.98      inference(demodulation,[status(thm)],[c_62560,c_62358]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62400,plain,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 19.56/2.98      inference(demodulation,[status(thm)],[c_62358,c_5093]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_7,plain,
% 19.56/2.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.56/2.98      inference(cnf_transformation,[],[f128]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_62404,plain,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 19.56/2.98      inference(demodulation,[status(thm)],[c_62400,c_7]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5727,plain,
% 19.56/2.98      ( X0 != X1
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X1
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4245]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_11443,plain,
% 19.56/2.98      ( k2_enumset1(X0,X1,X2,X3) != X4
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != X4
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(X0,X1,X2,X3) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5727]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_11444,plain,
% 19.56/2.98      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_11443]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_3,plain,
% 19.56/2.98      ( r1_tarski(k1_xboole_0,X0) ),
% 19.56/2.98      inference(cnf_transformation,[],[f64]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_10751,plain,
% 19.56/2.98      ( r1_tarski(k1_xboole_0,sK9) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_3]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_10752,plain,
% 19.56/2.98      ( r1_tarski(k1_xboole_0,sK9) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_10751]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_16,plain,
% 19.56/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.56/2.98      inference(cnf_transformation,[],[f79]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_6215,plain,
% 19.56/2.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0))
% 19.56/2.98      | r1_tarski(sK9,k1_xboole_0) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_16]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_6216,plain,
% 19.56/2.98      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.56/2.98      | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_6215]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_0,plain,
% 19.56/2.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.56/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5492,plain,
% 19.56/2.98      ( ~ r1_tarski(X0,sK9) | ~ r1_tarski(sK9,X0) | sK9 = X0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_0]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5493,plain,
% 19.56/2.98      ( sK9 = X0
% 19.56/2.98      | r1_tarski(X0,sK9) != iProver_top
% 19.56/2.98      | r1_tarski(sK9,X0) != iProver_top ),
% 19.56/2.98      inference(predicate_to_equality,[status(thm)],[c_5492]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5495,plain,
% 19.56/2.98      ( sK9 = k1_xboole_0
% 19.56/2.98      | r1_tarski(sK9,k1_xboole_0) != iProver_top
% 19.56/2.98      | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5493]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_4247,plain,
% 19.56/2.98      ( X0 != X1
% 19.56/2.98      | X2 != X3
% 19.56/2.98      | X4 != X5
% 19.56/2.98      | X6 != X7
% 19.56/2.98      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 19.56/2.98      theory(equality) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5292,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(X0,X1,X2,X3)
% 19.56/2.98      | sK9 != X0
% 19.56/2.98      | sK9 != X1
% 19.56/2.98      | sK9 != X2
% 19.56/2.98      | sK9 != X3 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_4247]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5293,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.56/2.98      | sK9 != k1_xboole_0 ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5292]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5194,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(X0,X1,X2,X3)
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(X0,X1,X2,X3) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5169]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(c_5195,plain,
% 19.56/2.98      ( k2_enumset1(sK9,sK9,sK9,sK9) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.56/2.98      | k2_enumset1(sK9,sK9,sK9,sK9) = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)
% 19.56/2.98      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 19.56/2.98      inference(instantiation,[status(thm)],[c_5194]) ).
% 19.56/2.98  
% 19.56/2.98  cnf(contradiction,plain,
% 19.56/2.98      ( $false ),
% 19.56/2.98      inference(minisat,
% 19.56/2.98                [status(thm)],
% 19.56/2.98                [c_62563,c_62404,c_61197,c_11444,c_10752,c_6216,c_5495,
% 19.56/2.98                 c_5293,c_5246,c_5195,c_5192,c_41]) ).
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.56/2.98  
% 19.56/2.98  ------                               Statistics
% 19.56/2.98  
% 19.56/2.98  ------ General
% 19.56/2.98  
% 19.56/2.98  abstr_ref_over_cycles:                  0
% 19.56/2.98  abstr_ref_under_cycles:                 0
% 19.56/2.98  gc_basic_clause_elim:                   0
% 19.56/2.98  forced_gc_time:                         0
% 19.56/2.98  parsing_time:                           0.011
% 19.56/2.98  unif_index_cands_time:                  0.
% 19.56/2.98  unif_index_add_time:                    0.
% 19.56/2.98  orderings_time:                         0.
% 19.56/2.98  out_proof_time:                         0.034
% 19.56/2.98  total_time:                             2.46
% 19.56/2.98  num_of_symbols:                         54
% 19.56/2.98  num_of_terms:                           46946
% 19.56/2.98  
% 19.56/2.98  ------ Preprocessing
% 19.56/2.98  
% 19.56/2.98  num_of_splits:                          0
% 19.56/2.98  num_of_split_atoms:                     0
% 19.56/2.98  num_of_reused_defs:                     0
% 19.56/2.98  num_eq_ax_congr_red:                    60
% 19.56/2.98  num_of_sem_filtered_clauses:            1
% 19.56/2.98  num_of_subtypes:                        0
% 19.56/2.98  monotx_restored_types:                  0
% 19.56/2.98  sat_num_of_epr_types:                   0
% 19.56/2.98  sat_num_of_non_cyclic_types:            0
% 19.56/2.98  sat_guarded_non_collapsed_types:        0
% 19.56/2.98  num_pure_diseq_elim:                    0
% 19.56/2.98  simp_replaced_by:                       0
% 19.56/2.98  res_preprocessed:                       204
% 19.56/2.98  prep_upred:                             0
% 19.56/2.98  prep_unflattend:                        118
% 19.56/2.98  smt_new_axioms:                         0
% 19.56/2.98  pred_elim_cands:                        8
% 19.56/2.98  pred_elim:                              2
% 19.56/2.98  pred_elim_cl:                           3
% 19.56/2.98  pred_elim_cycles:                       8
% 19.56/2.98  merged_defs:                            8
% 19.56/2.98  merged_defs_ncl:                        0
% 19.56/2.98  bin_hyper_res:                          8
% 19.56/2.98  prep_cycles:                            4
% 19.56/2.98  pred_elim_time:                         0.056
% 19.56/2.98  splitting_time:                         0.
% 19.56/2.98  sem_filter_time:                        0.
% 19.56/2.98  monotx_time:                            0.
% 19.56/2.98  subtype_inf_time:                       0.
% 19.56/2.98  
% 19.56/2.98  ------ Problem properties
% 19.56/2.98  
% 19.56/2.98  clauses:                                43
% 19.56/2.98  conjectures:                            6
% 19.56/2.98  epr:                                    6
% 19.56/2.98  horn:                                   34
% 19.56/2.98  ground:                                 6
% 19.56/2.98  unary:                                  10
% 19.56/2.98  binary:                                 7
% 19.56/2.98  lits:                                   121
% 19.56/2.98  lits_eq:                                22
% 19.56/2.98  fd_pure:                                0
% 19.56/2.98  fd_pseudo:                              0
% 19.56/2.98  fd_cond:                                5
% 19.56/2.98  fd_pseudo_cond:                         5
% 19.56/2.98  ac_symbols:                             0
% 19.56/2.98  
% 19.56/2.98  ------ Propositional Solver
% 19.56/2.98  
% 19.56/2.98  prop_solver_calls:                      32
% 19.56/2.98  prop_fast_solver_calls:                 4367
% 19.56/2.98  smt_solver_calls:                       0
% 19.56/2.98  smt_fast_solver_calls:                  0
% 19.56/2.98  prop_num_of_clauses:                    30074
% 19.56/2.98  prop_preprocess_simplified:             36208
% 19.56/2.98  prop_fo_subsumed:                       163
% 19.56/2.98  prop_solver_time:                       0.
% 19.56/2.98  smt_solver_time:                        0.
% 19.56/2.98  smt_fast_solver_time:                   0.
% 19.56/2.98  prop_fast_solver_time:                  0.
% 19.56/2.98  prop_unsat_core_time:                   0.002
% 19.56/2.98  
% 19.56/2.98  ------ QBF
% 19.56/2.98  
% 19.56/2.98  qbf_q_res:                              0
% 19.56/2.98  qbf_num_tautologies:                    0
% 19.56/2.98  qbf_prep_cycles:                        0
% 19.56/2.98  
% 19.56/2.98  ------ BMC1
% 19.56/2.98  
% 19.56/2.98  bmc1_current_bound:                     -1
% 19.56/2.98  bmc1_last_solved_bound:                 -1
% 19.56/2.98  bmc1_unsat_core_size:                   -1
% 19.56/2.98  bmc1_unsat_core_parents_size:           -1
% 19.56/2.98  bmc1_merge_next_fun:                    0
% 19.56/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.56/2.98  
% 19.56/2.98  ------ Instantiation
% 19.56/2.98  
% 19.56/2.98  inst_num_of_clauses:                    4913
% 19.56/2.98  inst_num_in_passive:                    423
% 19.56/2.98  inst_num_in_active:                     2305
% 19.56/2.98  inst_num_in_unprocessed:                2185
% 19.56/2.98  inst_num_of_loops:                      2720
% 19.56/2.98  inst_num_of_learning_restarts:          0
% 19.56/2.98  inst_num_moves_active_passive:          412
% 19.56/2.98  inst_lit_activity:                      0
% 19.56/2.98  inst_lit_activity_moves:                0
% 19.56/2.98  inst_num_tautologies:                   0
% 19.56/2.98  inst_num_prop_implied:                  0
% 19.56/2.98  inst_num_existing_simplified:           0
% 19.56/2.98  inst_num_eq_res_simplified:             0
% 19.56/2.98  inst_num_child_elim:                    0
% 19.56/2.98  inst_num_of_dismatching_blockings:      3968
% 19.56/2.98  inst_num_of_non_proper_insts:           9031
% 19.56/2.98  inst_num_of_duplicates:                 0
% 19.56/2.98  inst_inst_num_from_inst_to_res:         0
% 19.56/2.98  inst_dismatching_checking_time:         0.
% 19.56/2.98  
% 19.56/2.98  ------ Resolution
% 19.56/2.98  
% 19.56/2.98  res_num_of_clauses:                     0
% 19.56/2.98  res_num_in_passive:                     0
% 19.56/2.98  res_num_in_active:                      0
% 19.56/2.98  res_num_of_loops:                       208
% 19.56/2.98  res_forward_subset_subsumed:            706
% 19.56/2.98  res_backward_subset_subsumed:           0
% 19.56/2.98  res_forward_subsumed:                   0
% 19.56/2.98  res_backward_subsumed:                  0
% 19.56/2.98  res_forward_subsumption_resolution:     4
% 19.56/2.98  res_backward_subsumption_resolution:    0
% 19.56/2.98  res_clause_to_clause_subsumption:       17048
% 19.56/2.98  res_orphan_elimination:                 0
% 19.56/2.98  res_tautology_del:                      412
% 19.56/2.98  res_num_eq_res_simplified:              0
% 19.56/2.98  res_num_sel_changes:                    0
% 19.56/2.98  res_moves_from_active_to_pass:          0
% 19.56/2.98  
% 19.56/2.98  ------ Superposition
% 19.56/2.98  
% 19.56/2.98  sup_time_total:                         0.
% 19.56/2.98  sup_time_generating:                    0.
% 19.56/2.98  sup_time_sim_full:                      0.
% 19.56/2.98  sup_time_sim_immed:                     0.
% 19.56/2.98  
% 19.56/2.98  sup_num_of_clauses:                     3209
% 19.56/2.98  sup_num_in_active:                      156
% 19.56/2.98  sup_num_in_passive:                     3053
% 19.56/2.98  sup_num_of_loops:                       543
% 19.56/2.98  sup_fw_superposition:                   2547
% 19.56/2.98  sup_bw_superposition:                   3283
% 19.56/2.98  sup_immediate_simplified:               857
% 19.56/2.98  sup_given_eliminated:                   1
% 19.56/2.98  comparisons_done:                       0
% 19.56/2.98  comparisons_avoided:                    356
% 19.56/2.98  
% 19.56/2.98  ------ Simplifications
% 19.56/2.98  
% 19.56/2.98  
% 19.56/2.98  sim_fw_subset_subsumed:                 466
% 19.56/2.98  sim_bw_subset_subsumed:                 1098
% 19.56/2.98  sim_fw_subsumed:                        275
% 19.56/2.98  sim_bw_subsumed:                        38
% 19.56/2.98  sim_fw_subsumption_res:                 0
% 19.56/2.98  sim_bw_subsumption_res:                 0
% 19.56/2.98  sim_tautology_del:                      39
% 19.56/2.98  sim_eq_tautology_del:                   115
% 19.56/2.98  sim_eq_res_simp:                        1
% 19.56/2.98  sim_fw_demodulated:                     92
% 19.56/2.98  sim_bw_demodulated:                     298
% 19.56/2.98  sim_light_normalised:                   4
% 19.56/2.98  sim_joinable_taut:                      0
% 19.56/2.98  sim_joinable_simp:                      0
% 19.56/2.98  sim_ac_normalised:                      0
% 19.56/2.98  sim_smt_subsumption:                    0
% 19.56/2.98  
%------------------------------------------------------------------------------
