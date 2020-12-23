%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:47 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 976 expanded)
%              Number of clauses        :   86 ( 269 expanded)
%              Number of leaves         :   25 ( 221 expanded)
%              Depth                    :   26
%              Number of atoms          :  446 (2564 expanded)
%              Number of equality atoms :  202 ( 865 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f44])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f53])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f91])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f88,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f54])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f90])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1259,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1257,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2846,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1257])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1253,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1244,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_402,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_403,plain,
    ( ~ v5_relat_1(sK5,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X1),X0)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_relat_1(sK5)
    | X1 != X4
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_403])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_426,c_15])).

cnf(c_1241,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1509,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1241])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1245,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1516,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1245])).

cnf(c_2920,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1516])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_17,c_10])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_17,c_15,c_10])).

cnf(c_1242,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_1579,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_1244,c_1242])).

cnf(c_1249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1732,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1249])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1254,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2321,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1732,c_1254])).

cnf(c_2447,plain,
    ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1579,c_2321])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1255,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2398,plain,
    ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1732,c_1255])).

cnf(c_2593,plain,
    ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2447,c_2398])).

cnf(c_2923,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2920,c_2593])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1443,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1444,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_3350,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_34,c_1444])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1251,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2448,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | k9_relat_1(sK5,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1251])).

cnf(c_2678,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2447,c_2448])).

cnf(c_2682,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2678,c_1579])).

cnf(c_2683,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2682,c_1579])).

cnf(c_2696,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2683])).

cnf(c_2698,plain,
    ( sK5 = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2683,c_29,c_1443,c_2696])).

cnf(c_2699,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2698])).

cnf(c_3353,plain,
    ( sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3350,c_2699])).

cnf(c_3360,plain,
    ( sK5 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3353])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_591,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_593,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_29,c_28])).

cnf(c_3502,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_3360,c_593])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_relset_1(X1,X3,X2) != X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1248,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3713,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_1248])).

cnf(c_1537,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_856,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1699,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_860,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1482,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_3305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | X0 != sK5
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_3306,plain,
    ( X0 != sK5
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3305])).

cnf(c_3308,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k1_xboole_0 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3306])).

cnf(c_4110,plain,
    ( r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3713,c_29,c_34,c_1443,c_1444,c_1537,c_1699,c_2923,c_3308])).

cnf(c_4111,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4110])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1243,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_4118,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4111,c_1243])).

cnf(c_4122,plain,
    ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_4118])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1260,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4520,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4122,c_1260])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.87/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.00  
% 2.87/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.00  
% 2.87/1.00  ------  iProver source info
% 2.87/1.00  
% 2.87/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.00  git: non_committed_changes: false
% 2.87/1.00  git: last_make_outside_of_git: false
% 2.87/1.00  
% 2.87/1.00  ------ 
% 2.87/1.00  
% 2.87/1.00  ------ Input Options
% 2.87/1.00  
% 2.87/1.00  --out_options                           all
% 2.87/1.00  --tptp_safe_out                         true
% 2.87/1.00  --problem_path                          ""
% 2.87/1.00  --include_path                          ""
% 2.87/1.00  --clausifier                            res/vclausify_rel
% 2.87/1.00  --clausifier_options                    --mode clausify
% 2.87/1.00  --stdin                                 false
% 2.87/1.00  --stats_out                             all
% 2.87/1.00  
% 2.87/1.00  ------ General Options
% 2.87/1.00  
% 2.87/1.00  --fof                                   false
% 2.87/1.00  --time_out_real                         305.
% 2.87/1.00  --time_out_virtual                      -1.
% 2.87/1.00  --symbol_type_check                     false
% 2.87/1.00  --clausify_out                          false
% 2.87/1.00  --sig_cnt_out                           false
% 2.87/1.00  --trig_cnt_out                          false
% 2.87/1.00  --trig_cnt_out_tolerance                1.
% 2.87/1.00  --trig_cnt_out_sk_spl                   false
% 2.87/1.00  --abstr_cl_out                          false
% 2.87/1.00  
% 2.87/1.00  ------ Global Options
% 2.87/1.00  
% 2.87/1.00  --schedule                              default
% 2.87/1.00  --add_important_lit                     false
% 2.87/1.00  --prop_solver_per_cl                    1000
% 2.87/1.00  --min_unsat_core                        false
% 2.87/1.00  --soft_assumptions                      false
% 2.87/1.00  --soft_lemma_size                       3
% 2.87/1.00  --prop_impl_unit_size                   0
% 2.87/1.00  --prop_impl_unit                        []
% 2.87/1.00  --share_sel_clauses                     true
% 2.87/1.00  --reset_solvers                         false
% 2.87/1.00  --bc_imp_inh                            [conj_cone]
% 2.87/1.00  --conj_cone_tolerance                   3.
% 2.87/1.00  --extra_neg_conj                        none
% 2.87/1.00  --large_theory_mode                     true
% 2.87/1.00  --prolific_symb_bound                   200
% 2.87/1.00  --lt_threshold                          2000
% 2.87/1.00  --clause_weak_htbl                      true
% 2.87/1.00  --gc_record_bc_elim                     false
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing Options
% 2.87/1.00  
% 2.87/1.00  --preprocessing_flag                    true
% 2.87/1.00  --time_out_prep_mult                    0.1
% 2.87/1.00  --splitting_mode                        input
% 2.87/1.00  --splitting_grd                         true
% 2.87/1.00  --splitting_cvd                         false
% 2.87/1.00  --splitting_cvd_svl                     false
% 2.87/1.00  --splitting_nvd                         32
% 2.87/1.00  --sub_typing                            true
% 2.87/1.00  --prep_gs_sim                           true
% 2.87/1.00  --prep_unflatten                        true
% 2.87/1.00  --prep_res_sim                          true
% 2.87/1.00  --prep_upred                            true
% 2.87/1.00  --prep_sem_filter                       exhaustive
% 2.87/1.00  --prep_sem_filter_out                   false
% 2.87/1.00  --pred_elim                             true
% 2.87/1.00  --res_sim_input                         true
% 2.87/1.00  --eq_ax_congr_red                       true
% 2.87/1.00  --pure_diseq_elim                       true
% 2.87/1.00  --brand_transform                       false
% 2.87/1.00  --non_eq_to_eq                          false
% 2.87/1.00  --prep_def_merge                        true
% 2.87/1.00  --prep_def_merge_prop_impl              false
% 2.87/1.00  --prep_def_merge_mbd                    true
% 2.87/1.00  --prep_def_merge_tr_red                 false
% 2.87/1.00  --prep_def_merge_tr_cl                  false
% 2.87/1.00  --smt_preprocessing                     true
% 2.87/1.00  --smt_ac_axioms                         fast
% 2.87/1.00  --preprocessed_out                      false
% 2.87/1.00  --preprocessed_stats                    false
% 2.87/1.00  
% 2.87/1.00  ------ Abstraction refinement Options
% 2.87/1.00  
% 2.87/1.00  --abstr_ref                             []
% 2.87/1.00  --abstr_ref_prep                        false
% 2.87/1.00  --abstr_ref_until_sat                   false
% 2.87/1.00  --abstr_ref_sig_restrict                funpre
% 2.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.00  --abstr_ref_under                       []
% 2.87/1.00  
% 2.87/1.00  ------ SAT Options
% 2.87/1.00  
% 2.87/1.00  --sat_mode                              false
% 2.87/1.00  --sat_fm_restart_options                ""
% 2.87/1.00  --sat_gr_def                            false
% 2.87/1.00  --sat_epr_types                         true
% 2.87/1.00  --sat_non_cyclic_types                  false
% 2.87/1.00  --sat_finite_models                     false
% 2.87/1.00  --sat_fm_lemmas                         false
% 2.87/1.00  --sat_fm_prep                           false
% 2.87/1.00  --sat_fm_uc_incr                        true
% 2.87/1.00  --sat_out_model                         small
% 2.87/1.00  --sat_out_clauses                       false
% 2.87/1.00  
% 2.87/1.00  ------ QBF Options
% 2.87/1.00  
% 2.87/1.00  --qbf_mode                              false
% 2.87/1.00  --qbf_elim_univ                         false
% 2.87/1.00  --qbf_dom_inst                          none
% 2.87/1.00  --qbf_dom_pre_inst                      false
% 2.87/1.00  --qbf_sk_in                             false
% 2.87/1.00  --qbf_pred_elim                         true
% 2.87/1.00  --qbf_split                             512
% 2.87/1.00  
% 2.87/1.00  ------ BMC1 Options
% 2.87/1.00  
% 2.87/1.00  --bmc1_incremental                      false
% 2.87/1.00  --bmc1_axioms                           reachable_all
% 2.87/1.00  --bmc1_min_bound                        0
% 2.87/1.00  --bmc1_max_bound                        -1
% 2.87/1.00  --bmc1_max_bound_default                -1
% 2.87/1.00  --bmc1_symbol_reachability              true
% 2.87/1.00  --bmc1_property_lemmas                  false
% 2.87/1.00  --bmc1_k_induction                      false
% 2.87/1.00  --bmc1_non_equiv_states                 false
% 2.87/1.00  --bmc1_deadlock                         false
% 2.87/1.00  --bmc1_ucm                              false
% 2.87/1.00  --bmc1_add_unsat_core                   none
% 2.87/1.00  --bmc1_unsat_core_children              false
% 2.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.00  --bmc1_out_stat                         full
% 2.87/1.00  --bmc1_ground_init                      false
% 2.87/1.00  --bmc1_pre_inst_next_state              false
% 2.87/1.00  --bmc1_pre_inst_state                   false
% 2.87/1.00  --bmc1_pre_inst_reach_state             false
% 2.87/1.00  --bmc1_out_unsat_core                   false
% 2.87/1.00  --bmc1_aig_witness_out                  false
% 2.87/1.00  --bmc1_verbose                          false
% 2.87/1.00  --bmc1_dump_clauses_tptp                false
% 2.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.00  --bmc1_dump_file                        -
% 2.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.00  --bmc1_ucm_extend_mode                  1
% 2.87/1.00  --bmc1_ucm_init_mode                    2
% 2.87/1.00  --bmc1_ucm_cone_mode                    none
% 2.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.00  --bmc1_ucm_relax_model                  4
% 2.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.00  --bmc1_ucm_layered_model                none
% 2.87/1.00  --bmc1_ucm_max_lemma_size               10
% 2.87/1.00  
% 2.87/1.00  ------ AIG Options
% 2.87/1.00  
% 2.87/1.00  --aig_mode                              false
% 2.87/1.00  
% 2.87/1.00  ------ Instantiation Options
% 2.87/1.00  
% 2.87/1.00  --instantiation_flag                    true
% 2.87/1.00  --inst_sos_flag                         false
% 2.87/1.00  --inst_sos_phase                        true
% 2.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.00  --inst_lit_sel_side                     num_symb
% 2.87/1.00  --inst_solver_per_active                1400
% 2.87/1.00  --inst_solver_calls_frac                1.
% 2.87/1.00  --inst_passive_queue_type               priority_queues
% 2.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.00  --inst_passive_queues_freq              [25;2]
% 2.87/1.00  --inst_dismatching                      true
% 2.87/1.00  --inst_eager_unprocessed_to_passive     true
% 2.87/1.00  --inst_prop_sim_given                   true
% 2.87/1.00  --inst_prop_sim_new                     false
% 2.87/1.00  --inst_subs_new                         false
% 2.87/1.00  --inst_eq_res_simp                      false
% 2.87/1.00  --inst_subs_given                       false
% 2.87/1.00  --inst_orphan_elimination               true
% 2.87/1.00  --inst_learning_loop_flag               true
% 2.87/1.00  --inst_learning_start                   3000
% 2.87/1.00  --inst_learning_factor                  2
% 2.87/1.00  --inst_start_prop_sim_after_learn       3
% 2.87/1.00  --inst_sel_renew                        solver
% 2.87/1.00  --inst_lit_activity_flag                true
% 2.87/1.00  --inst_restr_to_given                   false
% 2.87/1.00  --inst_activity_threshold               500
% 2.87/1.00  --inst_out_proof                        true
% 2.87/1.00  
% 2.87/1.00  ------ Resolution Options
% 2.87/1.00  
% 2.87/1.00  --resolution_flag                       true
% 2.87/1.00  --res_lit_sel                           adaptive
% 2.87/1.00  --res_lit_sel_side                      none
% 2.87/1.00  --res_ordering                          kbo
% 2.87/1.00  --res_to_prop_solver                    active
% 2.87/1.00  --res_prop_simpl_new                    false
% 2.87/1.00  --res_prop_simpl_given                  true
% 2.87/1.00  --res_passive_queue_type                priority_queues
% 2.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.00  --res_passive_queues_freq               [15;5]
% 2.87/1.00  --res_forward_subs                      full
% 2.87/1.00  --res_backward_subs                     full
% 2.87/1.00  --res_forward_subs_resolution           true
% 2.87/1.00  --res_backward_subs_resolution          true
% 2.87/1.00  --res_orphan_elimination                true
% 2.87/1.00  --res_time_limit                        2.
% 2.87/1.00  --res_out_proof                         true
% 2.87/1.00  
% 2.87/1.00  ------ Superposition Options
% 2.87/1.00  
% 2.87/1.00  --superposition_flag                    true
% 2.87/1.00  --sup_passive_queue_type                priority_queues
% 2.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.00  --demod_completeness_check              fast
% 2.87/1.00  --demod_use_ground                      true
% 2.87/1.00  --sup_to_prop_solver                    passive
% 2.87/1.00  --sup_prop_simpl_new                    true
% 2.87/1.00  --sup_prop_simpl_given                  true
% 2.87/1.00  --sup_fun_splitting                     false
% 2.87/1.00  --sup_smt_interval                      50000
% 2.87/1.00  
% 2.87/1.00  ------ Superposition Simplification Setup
% 2.87/1.00  
% 2.87/1.00  --sup_indices_passive                   []
% 2.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_full_bw                           [BwDemod]
% 2.87/1.00  --sup_immed_triv                        [TrivRules]
% 2.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_immed_bw_main                     []
% 2.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.00  
% 2.87/1.00  ------ Combination Options
% 2.87/1.00  
% 2.87/1.00  --comb_res_mult                         3
% 2.87/1.00  --comb_sup_mult                         2
% 2.87/1.00  --comb_inst_mult                        10
% 2.87/1.00  
% 2.87/1.00  ------ Debug Options
% 2.87/1.00  
% 2.87/1.00  --dbg_backtrace                         false
% 2.87/1.00  --dbg_dump_prop_clauses                 false
% 2.87/1.00  --dbg_dump_prop_clauses_file            -
% 2.87/1.00  --dbg_out_stat                          false
% 2.87/1.00  ------ Parsing...
% 2.87/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.00  ------ Proving...
% 2.87/1.00  ------ Problem Properties 
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  clauses                                 24
% 2.87/1.00  conjectures                             3
% 2.87/1.00  EPR                                     3
% 2.87/1.00  Horn                                    20
% 2.87/1.00  unary                                   8
% 2.87/1.00  binary                                  4
% 2.87/1.00  lits                                    54
% 2.87/1.00  lits eq                                 19
% 2.87/1.00  fd_pure                                 0
% 2.87/1.00  fd_pseudo                               0
% 2.87/1.00  fd_cond                                 2
% 2.87/1.00  fd_pseudo_cond                          0
% 2.87/1.00  AC symbols                              0
% 2.87/1.00  
% 2.87/1.00  ------ Schedule dynamic 5 is on 
% 2.87/1.00  
% 2.87/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  ------ 
% 2.87/1.00  Current options:
% 2.87/1.00  ------ 
% 2.87/1.00  
% 2.87/1.00  ------ Input Options
% 2.87/1.00  
% 2.87/1.00  --out_options                           all
% 2.87/1.00  --tptp_safe_out                         true
% 2.87/1.00  --problem_path                          ""
% 2.87/1.00  --include_path                          ""
% 2.87/1.00  --clausifier                            res/vclausify_rel
% 2.87/1.00  --clausifier_options                    --mode clausify
% 2.87/1.00  --stdin                                 false
% 2.87/1.00  --stats_out                             all
% 2.87/1.00  
% 2.87/1.00  ------ General Options
% 2.87/1.00  
% 2.87/1.00  --fof                                   false
% 2.87/1.00  --time_out_real                         305.
% 2.87/1.00  --time_out_virtual                      -1.
% 2.87/1.00  --symbol_type_check                     false
% 2.87/1.00  --clausify_out                          false
% 2.87/1.00  --sig_cnt_out                           false
% 2.87/1.00  --trig_cnt_out                          false
% 2.87/1.00  --trig_cnt_out_tolerance                1.
% 2.87/1.00  --trig_cnt_out_sk_spl                   false
% 2.87/1.00  --abstr_cl_out                          false
% 2.87/1.00  
% 2.87/1.00  ------ Global Options
% 2.87/1.00  
% 2.87/1.00  --schedule                              default
% 2.87/1.00  --add_important_lit                     false
% 2.87/1.00  --prop_solver_per_cl                    1000
% 2.87/1.00  --min_unsat_core                        false
% 2.87/1.00  --soft_assumptions                      false
% 2.87/1.00  --soft_lemma_size                       3
% 2.87/1.00  --prop_impl_unit_size                   0
% 2.87/1.00  --prop_impl_unit                        []
% 2.87/1.00  --share_sel_clauses                     true
% 2.87/1.00  --reset_solvers                         false
% 2.87/1.00  --bc_imp_inh                            [conj_cone]
% 2.87/1.00  --conj_cone_tolerance                   3.
% 2.87/1.00  --extra_neg_conj                        none
% 2.87/1.00  --large_theory_mode                     true
% 2.87/1.00  --prolific_symb_bound                   200
% 2.87/1.00  --lt_threshold                          2000
% 2.87/1.00  --clause_weak_htbl                      true
% 2.87/1.00  --gc_record_bc_elim                     false
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing Options
% 2.87/1.00  
% 2.87/1.00  --preprocessing_flag                    true
% 2.87/1.00  --time_out_prep_mult                    0.1
% 2.87/1.00  --splitting_mode                        input
% 2.87/1.00  --splitting_grd                         true
% 2.87/1.00  --splitting_cvd                         false
% 2.87/1.00  --splitting_cvd_svl                     false
% 2.87/1.00  --splitting_nvd                         32
% 2.87/1.00  --sub_typing                            true
% 2.87/1.00  --prep_gs_sim                           true
% 2.87/1.00  --prep_unflatten                        true
% 2.87/1.00  --prep_res_sim                          true
% 2.87/1.00  --prep_upred                            true
% 2.87/1.00  --prep_sem_filter                       exhaustive
% 2.87/1.00  --prep_sem_filter_out                   false
% 2.87/1.00  --pred_elim                             true
% 2.87/1.00  --res_sim_input                         true
% 2.87/1.00  --eq_ax_congr_red                       true
% 2.87/1.00  --pure_diseq_elim                       true
% 2.87/1.00  --brand_transform                       false
% 2.87/1.00  --non_eq_to_eq                          false
% 2.87/1.00  --prep_def_merge                        true
% 2.87/1.00  --prep_def_merge_prop_impl              false
% 2.87/1.00  --prep_def_merge_mbd                    true
% 2.87/1.00  --prep_def_merge_tr_red                 false
% 2.87/1.00  --prep_def_merge_tr_cl                  false
% 2.87/1.00  --smt_preprocessing                     true
% 2.87/1.00  --smt_ac_axioms                         fast
% 2.87/1.00  --preprocessed_out                      false
% 2.87/1.00  --preprocessed_stats                    false
% 2.87/1.00  
% 2.87/1.00  ------ Abstraction refinement Options
% 2.87/1.00  
% 2.87/1.00  --abstr_ref                             []
% 2.87/1.00  --abstr_ref_prep                        false
% 2.87/1.00  --abstr_ref_until_sat                   false
% 2.87/1.00  --abstr_ref_sig_restrict                funpre
% 2.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.00  --abstr_ref_under                       []
% 2.87/1.00  
% 2.87/1.00  ------ SAT Options
% 2.87/1.00  
% 2.87/1.00  --sat_mode                              false
% 2.87/1.00  --sat_fm_restart_options                ""
% 2.87/1.00  --sat_gr_def                            false
% 2.87/1.00  --sat_epr_types                         true
% 2.87/1.00  --sat_non_cyclic_types                  false
% 2.87/1.00  --sat_finite_models                     false
% 2.87/1.00  --sat_fm_lemmas                         false
% 2.87/1.00  --sat_fm_prep                           false
% 2.87/1.00  --sat_fm_uc_incr                        true
% 2.87/1.00  --sat_out_model                         small
% 2.87/1.00  --sat_out_clauses                       false
% 2.87/1.00  
% 2.87/1.00  ------ QBF Options
% 2.87/1.00  
% 2.87/1.00  --qbf_mode                              false
% 2.87/1.00  --qbf_elim_univ                         false
% 2.87/1.00  --qbf_dom_inst                          none
% 2.87/1.00  --qbf_dom_pre_inst                      false
% 2.87/1.00  --qbf_sk_in                             false
% 2.87/1.00  --qbf_pred_elim                         true
% 2.87/1.00  --qbf_split                             512
% 2.87/1.00  
% 2.87/1.00  ------ BMC1 Options
% 2.87/1.00  
% 2.87/1.00  --bmc1_incremental                      false
% 2.87/1.00  --bmc1_axioms                           reachable_all
% 2.87/1.00  --bmc1_min_bound                        0
% 2.87/1.00  --bmc1_max_bound                        -1
% 2.87/1.00  --bmc1_max_bound_default                -1
% 2.87/1.00  --bmc1_symbol_reachability              true
% 2.87/1.00  --bmc1_property_lemmas                  false
% 2.87/1.00  --bmc1_k_induction                      false
% 2.87/1.00  --bmc1_non_equiv_states                 false
% 2.87/1.00  --bmc1_deadlock                         false
% 2.87/1.00  --bmc1_ucm                              false
% 2.87/1.00  --bmc1_add_unsat_core                   none
% 2.87/1.00  --bmc1_unsat_core_children              false
% 2.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.00  --bmc1_out_stat                         full
% 2.87/1.00  --bmc1_ground_init                      false
% 2.87/1.00  --bmc1_pre_inst_next_state              false
% 2.87/1.00  --bmc1_pre_inst_state                   false
% 2.87/1.00  --bmc1_pre_inst_reach_state             false
% 2.87/1.00  --bmc1_out_unsat_core                   false
% 2.87/1.00  --bmc1_aig_witness_out                  false
% 2.87/1.00  --bmc1_verbose                          false
% 2.87/1.00  --bmc1_dump_clauses_tptp                false
% 2.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.00  --bmc1_dump_file                        -
% 2.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.00  --bmc1_ucm_extend_mode                  1
% 2.87/1.00  --bmc1_ucm_init_mode                    2
% 2.87/1.00  --bmc1_ucm_cone_mode                    none
% 2.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.00  --bmc1_ucm_relax_model                  4
% 2.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.00  --bmc1_ucm_layered_model                none
% 2.87/1.00  --bmc1_ucm_max_lemma_size               10
% 2.87/1.00  
% 2.87/1.00  ------ AIG Options
% 2.87/1.00  
% 2.87/1.00  --aig_mode                              false
% 2.87/1.00  
% 2.87/1.00  ------ Instantiation Options
% 2.87/1.00  
% 2.87/1.00  --instantiation_flag                    true
% 2.87/1.00  --inst_sos_flag                         false
% 2.87/1.00  --inst_sos_phase                        true
% 2.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.00  --inst_lit_sel_side                     none
% 2.87/1.00  --inst_solver_per_active                1400
% 2.87/1.00  --inst_solver_calls_frac                1.
% 2.87/1.00  --inst_passive_queue_type               priority_queues
% 2.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.00  --inst_passive_queues_freq              [25;2]
% 2.87/1.00  --inst_dismatching                      true
% 2.87/1.00  --inst_eager_unprocessed_to_passive     true
% 2.87/1.00  --inst_prop_sim_given                   true
% 2.87/1.00  --inst_prop_sim_new                     false
% 2.87/1.00  --inst_subs_new                         false
% 2.87/1.00  --inst_eq_res_simp                      false
% 2.87/1.00  --inst_subs_given                       false
% 2.87/1.00  --inst_orphan_elimination               true
% 2.87/1.00  --inst_learning_loop_flag               true
% 2.87/1.00  --inst_learning_start                   3000
% 2.87/1.00  --inst_learning_factor                  2
% 2.87/1.00  --inst_start_prop_sim_after_learn       3
% 2.87/1.00  --inst_sel_renew                        solver
% 2.87/1.00  --inst_lit_activity_flag                true
% 2.87/1.00  --inst_restr_to_given                   false
% 2.87/1.00  --inst_activity_threshold               500
% 2.87/1.00  --inst_out_proof                        true
% 2.87/1.00  
% 2.87/1.00  ------ Resolution Options
% 2.87/1.00  
% 2.87/1.00  --resolution_flag                       false
% 2.87/1.00  --res_lit_sel                           adaptive
% 2.87/1.00  --res_lit_sel_side                      none
% 2.87/1.00  --res_ordering                          kbo
% 2.87/1.00  --res_to_prop_solver                    active
% 2.87/1.00  --res_prop_simpl_new                    false
% 2.87/1.00  --res_prop_simpl_given                  true
% 2.87/1.00  --res_passive_queue_type                priority_queues
% 2.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.00  --res_passive_queues_freq               [15;5]
% 2.87/1.00  --res_forward_subs                      full
% 2.87/1.00  --res_backward_subs                     full
% 2.87/1.00  --res_forward_subs_resolution           true
% 2.87/1.00  --res_backward_subs_resolution          true
% 2.87/1.00  --res_orphan_elimination                true
% 2.87/1.00  --res_time_limit                        2.
% 2.87/1.00  --res_out_proof                         true
% 2.87/1.00  
% 2.87/1.00  ------ Superposition Options
% 2.87/1.00  
% 2.87/1.00  --superposition_flag                    true
% 2.87/1.00  --sup_passive_queue_type                priority_queues
% 2.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.00  --demod_completeness_check              fast
% 2.87/1.00  --demod_use_ground                      true
% 2.87/1.00  --sup_to_prop_solver                    passive
% 2.87/1.00  --sup_prop_simpl_new                    true
% 2.87/1.00  --sup_prop_simpl_given                  true
% 2.87/1.00  --sup_fun_splitting                     false
% 2.87/1.00  --sup_smt_interval                      50000
% 2.87/1.00  
% 2.87/1.00  ------ Superposition Simplification Setup
% 2.87/1.00  
% 2.87/1.00  --sup_indices_passive                   []
% 2.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_full_bw                           [BwDemod]
% 2.87/1.00  --sup_immed_triv                        [TrivRules]
% 2.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_immed_bw_main                     []
% 2.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.00  
% 2.87/1.00  ------ Combination Options
% 2.87/1.00  
% 2.87/1.00  --comb_res_mult                         3
% 2.87/1.00  --comb_sup_mult                         2
% 2.87/1.00  --comb_inst_mult                        10
% 2.87/1.00  
% 2.87/1.00  ------ Debug Options
% 2.87/1.00  
% 2.87/1.00  --dbg_backtrace                         false
% 2.87/1.00  --dbg_dump_prop_clauses                 false
% 2.87/1.00  --dbg_dump_prop_clauses_file            -
% 2.87/1.00  --dbg_out_stat                          false
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  ------ Proving...
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  % SZS status Theorem for theBenchmark.p
% 2.87/1.00  
% 2.87/1.00   Resolution empty clause
% 2.87/1.00  
% 2.87/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.00  
% 2.87/1.00  fof(f6,axiom,(
% 2.87/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f44,plain,(
% 2.87/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.87/1.00    introduced(choice_axiom,[])).
% 2.87/1.00  
% 2.87/1.00  fof(f45,plain,(
% 2.87/1.00    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f44])).
% 2.87/1.00  
% 2.87/1.00  fof(f60,plain,(
% 2.87/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f45])).
% 2.87/1.00  
% 2.87/1.00  fof(f8,axiom,(
% 2.87/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f23,plain,(
% 2.87/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.87/1.00    inference(ennf_transformation,[],[f8])).
% 2.87/1.00  
% 2.87/1.00  fof(f24,plain,(
% 2.87/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.87/1.00    inference(flattening,[],[f23])).
% 2.87/1.00  
% 2.87/1.00  fof(f62,plain,(
% 2.87/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f24])).
% 2.87/1.00  
% 2.87/1.00  fof(f12,axiom,(
% 2.87/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f29,plain,(
% 2.87/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.87/1.00    inference(ennf_transformation,[],[f12])).
% 2.87/1.00  
% 2.87/1.00  fof(f46,plain,(
% 2.87/1.00    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.87/1.00    inference(nnf_transformation,[],[f29])).
% 2.87/1.00  
% 2.87/1.00  fof(f67,plain,(
% 2.87/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f46])).
% 2.87/1.00  
% 2.87/1.00  fof(f21,conjecture,(
% 2.87/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f22,negated_conjecture,(
% 2.87/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.87/1.00    inference(negated_conjecture,[],[f21])).
% 2.87/1.00  
% 2.87/1.00  fof(f42,plain,(
% 2.87/1.00    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.87/1.00    inference(ennf_transformation,[],[f22])).
% 2.87/1.00  
% 2.87/1.00  fof(f43,plain,(
% 2.87/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.87/1.00    inference(flattening,[],[f42])).
% 2.87/1.00  
% 2.87/1.00  fof(f53,plain,(
% 2.87/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.87/1.00    introduced(choice_axiom,[])).
% 2.87/1.00  
% 2.87/1.00  fof(f54,plain,(
% 2.87/1.00    ~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f53])).
% 2.87/1.00  
% 2.87/1.00  fof(f87,plain,(
% 2.87/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.87/1.00    inference(cnf_transformation,[],[f54])).
% 2.87/1.00  
% 2.87/1.00  fof(f2,axiom,(
% 2.87/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f56,plain,(
% 2.87/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f2])).
% 2.87/1.00  
% 2.87/1.00  fof(f3,axiom,(
% 2.87/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f57,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f3])).
% 2.87/1.00  
% 2.87/1.00  fof(f4,axiom,(
% 2.87/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f58,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f4])).
% 2.87/1.00  
% 2.87/1.00  fof(f90,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.87/1.00    inference(definition_unfolding,[],[f57,f58])).
% 2.87/1.00  
% 2.87/1.00  fof(f91,plain,(
% 2.87/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.87/1.00    inference(definition_unfolding,[],[f56,f90])).
% 2.87/1.00  
% 2.87/1.00  fof(f94,plain,(
% 2.87/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.87/1.00    inference(definition_unfolding,[],[f87,f91])).
% 2.87/1.00  
% 2.87/1.00  fof(f18,axiom,(
% 2.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f38,plain,(
% 2.87/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.00    inference(ennf_transformation,[],[f18])).
% 2.87/1.00  
% 2.87/1.00  fof(f75,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f38])).
% 2.87/1.00  
% 2.87/1.00  fof(f15,axiom,(
% 2.87/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f34,plain,(
% 2.87/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.87/1.00    inference(ennf_transformation,[],[f15])).
% 2.87/1.00  
% 2.87/1.00  fof(f35,plain,(
% 2.87/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/1.00    inference(flattening,[],[f34])).
% 2.87/1.00  
% 2.87/1.00  fof(f71,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f35])).
% 2.87/1.00  
% 2.87/1.00  fof(f85,plain,(
% 2.87/1.00    v1_funct_1(sK5)),
% 2.87/1.00    inference(cnf_transformation,[],[f54])).
% 2.87/1.00  
% 2.87/1.00  fof(f17,axiom,(
% 2.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f37,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.00    inference(ennf_transformation,[],[f17])).
% 2.87/1.00  
% 2.87/1.00  fof(f73,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f37])).
% 2.87/1.00  
% 2.87/1.00  fof(f89,plain,(
% 2.87/1.00    ~r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 2.87/1.00    inference(cnf_transformation,[],[f54])).
% 2.87/1.00  
% 2.87/1.00  fof(f74,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f38])).
% 2.87/1.00  
% 2.87/1.00  fof(f13,axiom,(
% 2.87/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f30,plain,(
% 2.87/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.87/1.00    inference(ennf_transformation,[],[f13])).
% 2.87/1.00  
% 2.87/1.00  fof(f31,plain,(
% 2.87/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/1.00    inference(flattening,[],[f30])).
% 2.87/1.00  
% 2.87/1.00  fof(f68,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f31])).
% 2.87/1.00  
% 2.87/1.00  fof(f11,axiom,(
% 2.87/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f28,plain,(
% 2.87/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.87/1.00    inference(ennf_transformation,[],[f11])).
% 2.87/1.00  
% 2.87/1.00  fof(f65,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f28])).
% 2.87/1.00  
% 2.87/1.00  fof(f10,axiom,(
% 2.87/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f27,plain,(
% 2.87/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.87/1.00    inference(ennf_transformation,[],[f10])).
% 2.87/1.00  
% 2.87/1.00  fof(f64,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f27])).
% 2.87/1.00  
% 2.87/1.00  fof(f93,plain,(
% 2.87/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.87/1.00    inference(definition_unfolding,[],[f64,f91])).
% 2.87/1.00  
% 2.87/1.00  fof(f14,axiom,(
% 2.87/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f32,plain,(
% 2.87/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.87/1.00    inference(ennf_transformation,[],[f14])).
% 2.87/1.00  
% 2.87/1.00  fof(f33,plain,(
% 2.87/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.87/1.00    inference(flattening,[],[f32])).
% 2.87/1.00  
% 2.87/1.00  fof(f70,plain,(
% 2.87/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f33])).
% 2.87/1.00  
% 2.87/1.00  fof(f20,axiom,(
% 2.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f40,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.00    inference(ennf_transformation,[],[f20])).
% 2.87/1.00  
% 2.87/1.00  fof(f41,plain,(
% 2.87/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.00    inference(flattening,[],[f40])).
% 2.87/1.00  
% 2.87/1.00  fof(f52,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.00    inference(nnf_transformation,[],[f41])).
% 2.87/1.00  
% 2.87/1.00  fof(f79,plain,(
% 2.87/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f52])).
% 2.87/1.00  
% 2.87/1.00  fof(f86,plain,(
% 2.87/1.00    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.87/1.00    inference(cnf_transformation,[],[f54])).
% 2.87/1.00  
% 2.87/1.00  fof(f95,plain,(
% 2.87/1.00    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.87/1.00    inference(definition_unfolding,[],[f86,f91])).
% 2.87/1.00  
% 2.87/1.00  fof(f88,plain,(
% 2.87/1.00    k1_xboole_0 != sK4),
% 2.87/1.00    inference(cnf_transformation,[],[f54])).
% 2.87/1.00  
% 2.87/1.00  fof(f19,axiom,(
% 2.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f39,plain,(
% 2.87/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/1.00    inference(ennf_transformation,[],[f19])).
% 2.87/1.00  
% 2.87/1.00  fof(f47,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/1.00    inference(nnf_transformation,[],[f39])).
% 2.87/1.00  
% 2.87/1.00  fof(f48,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/1.00    inference(rectify,[],[f47])).
% 2.87/1.00  
% 2.87/1.00  fof(f50,plain,(
% 2.87/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 2.87/1.00    introduced(choice_axiom,[])).
% 2.87/1.00  
% 2.87/1.00  fof(f49,plain,(
% 2.87/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 2.87/1.00    introduced(choice_axiom,[])).
% 2.87/1.00  
% 2.87/1.00  fof(f51,plain,(
% 2.87/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 2.87/1.00  
% 2.87/1.00  fof(f78,plain,(
% 2.87/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f51])).
% 2.87/1.00  
% 2.87/1.00  fof(f1,axiom,(
% 2.87/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f55,plain,(
% 2.87/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f1])).
% 2.87/1.00  
% 2.87/1.00  fof(f16,axiom,(
% 2.87/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f36,plain,(
% 2.87/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.87/1.00    inference(ennf_transformation,[],[f16])).
% 2.87/1.00  
% 2.87/1.00  fof(f72,plain,(
% 2.87/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.87/1.00    inference(cnf_transformation,[],[f36])).
% 2.87/1.00  
% 2.87/1.00  fof(f5,axiom,(
% 2.87/1.00    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 2.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.00  
% 2.87/1.00  fof(f59,plain,(
% 2.87/1.00    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 2.87/1.00    inference(cnf_transformation,[],[f5])).
% 2.87/1.00  
% 2.87/1.00  fof(f92,plain,(
% 2.87/1.00    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 2.87/1.00    inference(definition_unfolding,[],[f59,f90])).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2,plain,
% 2.87/1.00      ( m1_subset_1(sK0(X0),X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1259,plain,
% 2.87/1.00      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4,plain,
% 2.87/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.87/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1257,plain,
% 2.87/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.87/1.00      | m1_subset_1(X0,X1) != iProver_top
% 2.87/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2846,plain,
% 2.87/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1259,c_1257]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_8,plain,
% 2.87/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.87/1.00      | ~ v1_relat_1(X1)
% 2.87/1.00      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.87/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1253,plain,
% 2.87/1.00      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.87/1.00      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.87/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_29,negated_conjecture,
% 2.87/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1244,plain,
% 2.87/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_16,plain,
% 2.87/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_13,plain,
% 2.87/1.00      ( ~ v5_relat_1(X0,X1)
% 2.87/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.87/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_31,negated_conjecture,
% 2.87/1.00      ( v1_funct_1(sK5) ),
% 2.87/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_402,plain,
% 2.87/1.00      ( ~ v5_relat_1(X0,X1)
% 2.87/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.87/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | sK5 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_403,plain,
% 2.87/1.00      ( ~ v5_relat_1(sK5,X0)
% 2.87/1.00      | ~ r2_hidden(X1,k1_relat_1(sK5))
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X1),X0)
% 2.87/1.00      | ~ v1_relat_1(sK5) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_402]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_425,plain,
% 2.87/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 2.87/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.87/1.00      | ~ v1_relat_1(sK5)
% 2.87/1.00      | X1 != X4
% 2.87/1.00      | sK5 != X2 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_403]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_426,plain,
% 2.87/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 2.87/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.87/1.00      | ~ v1_relat_1(sK5) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_15,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_438,plain,
% 2.87/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 2.87/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.87/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_426,c_15]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1241,plain,
% 2.87/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X0),X1) = iProver_top
% 2.87/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1509,plain,
% 2.87/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.87/1.00      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1244,c_1241]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_27,negated_conjecture,
% 2.87/1.00      ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
% 2.87/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1245,plain,
% 2.87/1.00      ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1516,plain,
% 2.87/1.00      ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1509,c_1245]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2920,plain,
% 2.87/1.00      ( k11_relat_1(sK5,sK3) = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1253,c_1516]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_17,plain,
% 2.87/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_10,plain,
% 2.87/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_382,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.00      inference(resolution,[status(thm)],[c_17,c_10]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_386,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_382,c_17,c_15,c_10]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1242,plain,
% 2.87/1.00      ( k7_relat_1(X0,X1) = X0
% 2.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1579,plain,
% 2.87/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1244,c_1242]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1249,plain,
% 2.87/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.87/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1732,plain,
% 2.87/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1244,c_1249]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_7,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.87/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1254,plain,
% 2.87/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.87/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2321,plain,
% 2.87/1.00      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1732,c_1254]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2447,plain,
% 2.87/1.00      ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1579,c_2321]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_6,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.87/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1255,plain,
% 2.87/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.87/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2398,plain,
% 2.87/1.00      ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1732,c_1255]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2593,plain,
% 2.87/1.00      ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2447,c_2398]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2923,plain,
% 2.87/1.00      ( k2_relat_1(sK5) = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2920,c_2593]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_34,plain,
% 2.87/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1443,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.87/1.00      | v1_relat_1(sK5) ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1444,plain,
% 2.87/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.87/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3350,plain,
% 2.87/1.00      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2923,c_34,c_1444]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_11,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.87/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1251,plain,
% 2.87/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.87/1.00      | k1_xboole_0 = X0
% 2.87/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2448,plain,
% 2.87/1.00      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 2.87/1.00      | k9_relat_1(sK5,X0) != k1_xboole_0
% 2.87/1.01      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_2321,c_1251]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2678,plain,
% 2.87/1.01      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 2.87/1.01      | k2_relat_1(sK5) != k1_xboole_0
% 2.87/1.01      | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_2447,c_2448]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2682,plain,
% 2.87/1.01      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 2.87/1.01      | k2_relat_1(sK5) != k1_xboole_0
% 2.87/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.01      inference(light_normalisation,[status(thm)],[c_2678,c_1579]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2683,plain,
% 2.87/1.01      ( k2_relat_1(sK5) != k1_xboole_0
% 2.87/1.01      | sK5 = k1_xboole_0
% 2.87/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.01      inference(demodulation,[status(thm)],[c_2682,c_1579]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2696,plain,
% 2.87/1.01      ( ~ v1_relat_1(sK5)
% 2.87/1.01      | k2_relat_1(sK5) != k1_xboole_0
% 2.87/1.01      | sK5 = k1_xboole_0 ),
% 2.87/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2683]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2698,plain,
% 2.87/1.01      ( sK5 = k1_xboole_0 | k2_relat_1(sK5) != k1_xboole_0 ),
% 2.87/1.01      inference(global_propositional_subsumption,
% 2.87/1.01                [status(thm)],
% 2.87/1.01                [c_2683,c_29,c_1443,c_2696]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2699,plain,
% 2.87/1.01      ( k2_relat_1(sK5) != k1_xboole_0 | sK5 = k1_xboole_0 ),
% 2.87/1.01      inference(renaming,[status(thm)],[c_2698]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3353,plain,
% 2.87/1.01      ( sK5 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.01      inference(demodulation,[status(thm)],[c_3350,c_2699]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3360,plain,
% 2.87/1.01      ( sK5 = k1_xboole_0 ),
% 2.87/1.01      inference(equality_resolution_simp,[status(thm)],[c_3353]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_26,plain,
% 2.87/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.01      | k1_xboole_0 = X2 ),
% 2.87/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_30,negated_conjecture,
% 2.87/1.01      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.87/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_590,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.01      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.87/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.01      | sK4 != X2
% 2.87/1.01      | sK5 != X0
% 2.87/1.01      | k1_xboole_0 = X2 ),
% 2.87/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_591,plain,
% 2.87/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.87/1.01      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.87/1.01      | k1_xboole_0 = sK4 ),
% 2.87/1.01      inference(unflattening,[status(thm)],[c_590]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_28,negated_conjecture,
% 2.87/1.01      ( k1_xboole_0 != sK4 ),
% 2.87/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_593,plain,
% 2.87/1.01      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.87/1.01      inference(global_propositional_subsumption,
% 2.87/1.01                [status(thm)],
% 2.87/1.01                [c_591,c_29,c_28]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3502,plain,
% 2.87/1.01      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.87/1.01      inference(demodulation,[status(thm)],[c_3360,c_593]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_18,plain,
% 2.87/1.01      ( ~ r2_hidden(X0,X1)
% 2.87/1.01      | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
% 2.87/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.87/1.01      | k1_relset_1(X1,X3,X2) != X1 ),
% 2.87/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1248,plain,
% 2.87/1.01      ( k1_relset_1(X0,X1,X2) != X0
% 2.87/1.01      | r2_hidden(X3,X0) != iProver_top
% 2.87/1.01      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top
% 2.87/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3713,plain,
% 2.87/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.87/1.01      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 2.87/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_3502,c_1248]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1537,plain,
% 2.87/1.01      ( ~ v1_relat_1(sK5)
% 2.87/1.01      | k2_relat_1(sK5) != k1_xboole_0
% 2.87/1.01      | k1_xboole_0 = sK5 ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_856,plain,( X0 = X0 ),theory(equality) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1699,plain,
% 2.87/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_856]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_860,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.87/1.01      theory(equality) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1482,plain,
% 2.87/1.01      ( m1_subset_1(X0,X1)
% 2.87/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.87/1.01      | X1 != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.87/1.01      | X0 != sK5 ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_860]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3305,plain,
% 2.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.87/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.87/1.01      | X0 != sK5
% 2.87/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_1482]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3306,plain,
% 2.87/1.01      ( X0 != sK5
% 2.87/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.87/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
% 2.87/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_3305]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3308,plain,
% 2.87/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.87/1.01      | k1_xboole_0 != sK5
% 2.87/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 2.87/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_3306]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_4110,plain,
% 2.87/1.01      ( r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 2.87/1.01      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.87/1.01      inference(global_propositional_subsumption,
% 2.87/1.01                [status(thm)],
% 2.87/1.01                [c_3713,c_29,c_34,c_1443,c_1444,c_1537,c_1699,c_2923,c_3308]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_4111,plain,
% 2.87/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.87/1.01      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.87/1.01      inference(renaming,[status(thm)],[c_4110]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_0,plain,
% 2.87/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.87/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_14,plain,
% 2.87/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.87/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_357,plain,
% 2.87/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.87/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_358,plain,
% 2.87/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.87/1.01      inference(unflattening,[status(thm)],[c_357]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1243,plain,
% 2.87/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_4118,plain,
% 2.87/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.87/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4111,c_1243]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_4122,plain,
% 2.87/1.01      ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_2846,c_4118]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1,plain,
% 2.87/1.01      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 2.87/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1260,plain,
% 2.87/1.01      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_4520,plain,
% 2.87/1.01      ( $false ),
% 2.87/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4122,c_1260]) ).
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.01  
% 2.87/1.01  ------                               Statistics
% 2.87/1.01  
% 2.87/1.01  ------ General
% 2.87/1.01  
% 2.87/1.01  abstr_ref_over_cycles:                  0
% 2.87/1.01  abstr_ref_under_cycles:                 0
% 2.87/1.01  gc_basic_clause_elim:                   0
% 2.87/1.01  forced_gc_time:                         0
% 2.87/1.01  parsing_time:                           0.01
% 2.87/1.01  unif_index_cands_time:                  0.
% 2.87/1.01  unif_index_add_time:                    0.
% 2.87/1.01  orderings_time:                         0.
% 2.87/1.01  out_proof_time:                         0.012
% 2.87/1.01  total_time:                             0.133
% 2.87/1.01  num_of_symbols:                         58
% 2.87/1.01  num_of_terms:                           5621
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing
% 2.87/1.01  
% 2.87/1.01  num_of_splits:                          0
% 2.87/1.01  num_of_split_atoms:                     0
% 2.87/1.01  num_of_reused_defs:                     0
% 2.87/1.01  num_eq_ax_congr_red:                    41
% 2.87/1.01  num_of_sem_filtered_clauses:            1
% 2.87/1.01  num_of_subtypes:                        0
% 2.87/1.01  monotx_restored_types:                  0
% 2.87/1.01  sat_num_of_epr_types:                   0
% 2.87/1.01  sat_num_of_non_cyclic_types:            0
% 2.87/1.01  sat_guarded_non_collapsed_types:        0
% 2.87/1.01  num_pure_diseq_elim:                    0
% 2.87/1.01  simp_replaced_by:                       0
% 2.87/1.01  res_preprocessed:                       133
% 2.87/1.01  prep_upred:                             0
% 2.87/1.01  prep_unflattend:                        38
% 2.87/1.01  smt_new_axioms:                         0
% 2.87/1.01  pred_elim_cands:                        4
% 2.87/1.01  pred_elim:                              5
% 2.87/1.01  pred_elim_cl:                           8
% 2.87/1.01  pred_elim_cycles:                       10
% 2.87/1.01  merged_defs:                            0
% 2.87/1.01  merged_defs_ncl:                        0
% 2.87/1.01  bin_hyper_res:                          0
% 2.87/1.01  prep_cycles:                            4
% 2.87/1.01  pred_elim_time:                         0.007
% 2.87/1.01  splitting_time:                         0.
% 2.87/1.01  sem_filter_time:                        0.
% 2.87/1.01  monotx_time:                            0.
% 2.87/1.01  subtype_inf_time:                       0.
% 2.87/1.01  
% 2.87/1.01  ------ Problem properties
% 2.87/1.01  
% 2.87/1.01  clauses:                                24
% 2.87/1.01  conjectures:                            3
% 2.87/1.01  epr:                                    3
% 2.87/1.01  horn:                                   20
% 2.87/1.01  ground:                                 6
% 2.87/1.01  unary:                                  8
% 2.87/1.01  binary:                                 4
% 2.87/1.01  lits:                                   54
% 2.87/1.01  lits_eq:                                19
% 2.87/1.01  fd_pure:                                0
% 2.87/1.01  fd_pseudo:                              0
% 2.87/1.01  fd_cond:                                2
% 2.87/1.01  fd_pseudo_cond:                         0
% 2.87/1.01  ac_symbols:                             0
% 2.87/1.01  
% 2.87/1.01  ------ Propositional Solver
% 2.87/1.01  
% 2.87/1.01  prop_solver_calls:                      27
% 2.87/1.01  prop_fast_solver_calls:                 840
% 2.87/1.01  smt_solver_calls:                       0
% 2.87/1.01  smt_fast_solver_calls:                  0
% 2.87/1.01  prop_num_of_clauses:                    1731
% 2.87/1.01  prop_preprocess_simplified:             5528
% 2.87/1.01  prop_fo_subsumed:                       10
% 2.87/1.01  prop_solver_time:                       0.
% 2.87/1.01  smt_solver_time:                        0.
% 2.87/1.01  smt_fast_solver_time:                   0.
% 2.87/1.01  prop_fast_solver_time:                  0.
% 2.87/1.01  prop_unsat_core_time:                   0.
% 2.87/1.01  
% 2.87/1.01  ------ QBF
% 2.87/1.01  
% 2.87/1.01  qbf_q_res:                              0
% 2.87/1.01  qbf_num_tautologies:                    0
% 2.87/1.01  qbf_prep_cycles:                        0
% 2.87/1.01  
% 2.87/1.01  ------ BMC1
% 2.87/1.01  
% 2.87/1.01  bmc1_current_bound:                     -1
% 2.87/1.01  bmc1_last_solved_bound:                 -1
% 2.87/1.01  bmc1_unsat_core_size:                   -1
% 2.87/1.01  bmc1_unsat_core_parents_size:           -1
% 2.87/1.01  bmc1_merge_next_fun:                    0
% 2.87/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.01  
% 2.87/1.01  ------ Instantiation
% 2.87/1.01  
% 2.87/1.01  inst_num_of_clauses:                    509
% 2.87/1.01  inst_num_in_passive:                    38
% 2.87/1.01  inst_num_in_active:                     287
% 2.87/1.01  inst_num_in_unprocessed:                184
% 2.87/1.01  inst_num_of_loops:                      330
% 2.87/1.01  inst_num_of_learning_restarts:          0
% 2.87/1.01  inst_num_moves_active_passive:          40
% 2.87/1.01  inst_lit_activity:                      0
% 2.87/1.01  inst_lit_activity_moves:                0
% 2.87/1.01  inst_num_tautologies:                   0
% 2.87/1.01  inst_num_prop_implied:                  0
% 2.87/1.01  inst_num_existing_simplified:           0
% 2.87/1.01  inst_num_eq_res_simplified:             0
% 2.87/1.01  inst_num_child_elim:                    0
% 2.87/1.01  inst_num_of_dismatching_blockings:      227
% 2.87/1.01  inst_num_of_non_proper_insts:           405
% 2.87/1.01  inst_num_of_duplicates:                 0
% 2.87/1.01  inst_inst_num_from_inst_to_res:         0
% 2.87/1.01  inst_dismatching_checking_time:         0.
% 2.87/1.01  
% 2.87/1.01  ------ Resolution
% 2.87/1.01  
% 2.87/1.01  res_num_of_clauses:                     0
% 2.87/1.01  res_num_in_passive:                     0
% 2.87/1.01  res_num_in_active:                      0
% 2.87/1.01  res_num_of_loops:                       137
% 2.87/1.01  res_forward_subset_subsumed:            27
% 2.87/1.01  res_backward_subset_subsumed:           0
% 2.87/1.01  res_forward_subsumed:                   0
% 2.87/1.01  res_backward_subsumed:                  0
% 2.87/1.01  res_forward_subsumption_resolution:     1
% 2.87/1.01  res_backward_subsumption_resolution:    0
% 2.87/1.01  res_clause_to_clause_subsumption:       122
% 2.87/1.01  res_orphan_elimination:                 0
% 2.87/1.01  res_tautology_del:                      32
% 2.87/1.01  res_num_eq_res_simplified:              0
% 2.87/1.01  res_num_sel_changes:                    0
% 2.87/1.01  res_moves_from_active_to_pass:          0
% 2.87/1.01  
% 2.87/1.01  ------ Superposition
% 2.87/1.01  
% 2.87/1.01  sup_time_total:                         0.
% 2.87/1.01  sup_time_generating:                    0.
% 2.87/1.01  sup_time_sim_full:                      0.
% 2.87/1.01  sup_time_sim_immed:                     0.
% 2.87/1.01  
% 2.87/1.01  sup_num_of_clauses:                     60
% 2.87/1.01  sup_num_in_active:                      41
% 2.87/1.01  sup_num_in_passive:                     19
% 2.87/1.01  sup_num_of_loops:                       64
% 2.87/1.01  sup_fw_superposition:                   37
% 2.87/1.01  sup_bw_superposition:                   20
% 2.87/1.01  sup_immediate_simplified:               21
% 2.87/1.01  sup_given_eliminated:                   0
% 2.87/1.01  comparisons_done:                       0
% 2.87/1.01  comparisons_avoided:                    0
% 2.87/1.01  
% 2.87/1.01  ------ Simplifications
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  sim_fw_subset_subsumed:                 11
% 2.87/1.01  sim_bw_subset_subsumed:                 1
% 2.87/1.01  sim_fw_subsumed:                        4
% 2.87/1.01  sim_bw_subsumed:                        0
% 2.87/1.01  sim_fw_subsumption_res:                 3
% 2.87/1.01  sim_bw_subsumption_res:                 0
% 2.87/1.01  sim_tautology_del:                      0
% 2.87/1.01  sim_eq_tautology_del:                   2
% 2.87/1.01  sim_eq_res_simp:                        1
% 2.87/1.01  sim_fw_demodulated:                     5
% 2.87/1.01  sim_bw_demodulated:                     25
% 2.87/1.01  sim_light_normalised:                   2
% 2.87/1.01  sim_joinable_taut:                      0
% 2.87/1.01  sim_joinable_simp:                      0
% 2.87/1.01  sim_ac_normalised:                      0
% 2.87/1.01  sim_smt_subsumption:                    0
% 2.87/1.01  
%------------------------------------------------------------------------------
