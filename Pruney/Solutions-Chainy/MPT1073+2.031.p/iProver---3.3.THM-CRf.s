%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:06 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  183 (5408 expanded)
%              Number of clauses        :  126 (1982 expanded)
%              Number of leaves         :   19 (1020 expanded)
%              Depth                    :   27
%              Number of atoms          :  549 (23033 expanded)
%              Number of equality atoms :  300 (6285 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK1
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK1
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f35])).

fof(f60,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK1
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_12357,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4748,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
    | X0 != sK0(sK1,k1_relat_1(sK4),sK4)
    | X1 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_11352,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),X0)
    | ~ m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
    | X0 != k1_relat_1(sK4)
    | sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4748])).

cnf(c_11353,plain,
    ( X0 != k1_relat_1(sK4)
    | sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4)
    | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),X0) = iProver_top
    | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11352])).

cnf(c_11355,plain,
    ( sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4)
    | k1_xboole_0 != k1_relat_1(sK4)
    | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11353])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_895,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_897,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_24])).

cnf(c_1842,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1846,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2431,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1842,c_1846])).

cnf(c_2704,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_897,c_2431])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1845,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2358,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1842,c_1845])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1843,plain,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2421,plain,
    ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2358,c_1843])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2300,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1847])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1848,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2304,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2300,c_1848])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1850,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_302,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_303,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_1840,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_304,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1999,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2025,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1840,c_29,c_304,c_1999])).

cnf(c_2026,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2025])).

cnf(c_2611,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_2026])).

cnf(c_2831,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2611,c_29,c_1999])).

cnf(c_2832,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2831])).

cnf(c_2841,plain,
    ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_2832])).

cnf(c_2965,plain,
    ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
    inference(superposition,[status(thm)],[c_2421,c_2841])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1844,plain,
    ( k1_funct_1(sK4,X0) != sK1
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3206,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2965,c_1844])).

cnf(c_3258,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_3206])).

cnf(c_30,plain,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1505,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2089,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_1506,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2122,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK2,sK3,sK4)
    | k2_relset_1(sK2,sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2214,plain,
    ( X0 = k2_relset_1(sK2,sK3,sK4)
    | X0 != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2243,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = k2_relset_1(sK2,sK3,sK4)
    | k2_relat_1(sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2244,plain,
    ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_1507,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2014,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    | X1 != k2_relset_1(sK2,sK3,sK4)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2088,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    | X0 != k2_relset_1(sK2,sK3,sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_2371,plain,
    ( ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK1,k2_relat_1(sK4))
    | k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_2372,plain,
    ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
    | sK1 != sK1
    | r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1849,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2752,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_1849])).

cnf(c_2947,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2752,c_29,c_1999])).

cnf(c_2948,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2947])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1853,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2956,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_1853])).

cnf(c_3257,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_3206])).

cnf(c_3265,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3257,c_2304])).

cnf(c_3271,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3258,c_24,c_30,c_2011,c_2089,c_2243,c_2244,c_2372,c_3265])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_862,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_1837,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_3276,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3271,c_1837])).

cnf(c_3288,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3276])).

cnf(c_3279,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3271,c_1842])).

cnf(c_3292,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3288,c_3279])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_882,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_1836,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_3277,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3271,c_1836])).

cnf(c_3972,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_3277])).

cnf(c_3975,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_3279])).

cnf(c_3997,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3972,c_3975])).

cnf(c_3274,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3271,c_2431])).

cnf(c_3974,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3292,c_3274])).

cnf(c_6327,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3997,c_3974])).

cnf(c_6307,plain,
    ( sK0(sK1,k1_relat_1(sK4),sK4) = sK0(sK1,k1_relat_1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_5886,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK4)
    | k1_relat_1(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_5887,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5886])).

cnf(c_5782,plain,
    ( X0 != X1
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_5783,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5782])).

cnf(c_3976,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_3206])).

cnf(c_2565,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,k2_relat_1(sK4))
    | X1 != k2_relat_1(sK4)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_3345,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k2_relat_1(sK4))
    | X0 != k2_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_3347,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK4))
    | r2_hidden(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3345])).

cnf(c_3017,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3018,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3017])).

cnf(c_2046,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(sK0(X0,X1,sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2583,plain,
    ( r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_2584,plain,
    ( r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_1513,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2400,plain,
    ( k2_relat_1(sK4) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_2402,plain,
    ( k2_relat_1(sK4) = k2_relat_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_2245,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK4)
    | k2_relat_1(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2399,plain,
    ( X0 != k2_relat_1(X1)
    | X0 = k2_relat_1(sK4)
    | k2_relat_1(sK4) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2401,plain,
    ( k2_relat_1(sK4) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK4)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_2379,plain,
    ( ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4)))
    | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relset_1(sK2,sK3,sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_2380,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relset_1(sK2,sK3,sK4)
    | sK1 != sK1
    | r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_2252,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relset_1(sK2,sK3,sK4)
    | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2061,plain,
    ( ~ v1_relat_1(sK4)
    | k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1532,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12357,c_11355,c_6327,c_6307,c_5887,c_5783,c_3976,c_3347,c_3018,c_2584,c_2402,c_2401,c_2380,c_2371,c_2252,c_2244,c_2243,c_2089,c_2061,c_2011,c_1999,c_1998,c_1532,c_8,c_30,c_23,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.55/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/1.00  
% 3.55/1.00  ------  iProver source info
% 3.55/1.00  
% 3.55/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.55/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/1.00  git: non_committed_changes: false
% 3.55/1.00  git: last_make_outside_of_git: false
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    --mode clausify
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         false
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     num_symb
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       true
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.00  --demod_use_ground                      true
% 3.55/1.00  --sup_to_prop_solver                    passive
% 3.55/1.00  --sup_prop_simpl_new                    true
% 3.55/1.00  --sup_prop_simpl_given                  true
% 3.55/1.00  --sup_fun_splitting                     false
% 3.55/1.00  --sup_smt_interval                      50000
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Simplification Setup
% 3.55/1.00  
% 3.55/1.00  --sup_indices_passive                   []
% 3.55/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.00  --sup_full_bw                           [BwDemod]
% 3.55/1.00  --sup_immed_triv                        [TrivRules]
% 3.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.00  --sup_immed_bw_main                     []
% 3.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/1.00  
% 3.55/1.00  ------ Combination Options
% 3.55/1.00  
% 3.55/1.00  --comb_res_mult                         3
% 3.55/1.00  --comb_sup_mult                         2
% 3.55/1.00  --comb_inst_mult                        10
% 3.55/1.00  
% 3.55/1.00  ------ Debug Options
% 3.55/1.00  
% 3.55/1.00  --dbg_backtrace                         false
% 3.55/1.00  --dbg_dump_prop_clauses                 false
% 3.55/1.00  --dbg_dump_prop_clauses_file            -
% 3.55/1.00  --dbg_out_stat                          false
% 3.55/1.00  ------ Parsing...
% 3.55/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/1.00  ------ Proving...
% 3.55/1.00  ------ Problem Properties 
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  clauses                                 21
% 3.55/1.00  conjectures                             3
% 3.55/1.00  EPR                                     2
% 3.55/1.00  Horn                                    19
% 3.55/1.00  unary                                   5
% 3.55/1.00  binary                                  7
% 3.55/1.00  lits                                    49
% 3.55/1.00  lits eq                                 14
% 3.55/1.00  fd_pure                                 0
% 3.55/1.00  fd_pseudo                               0
% 3.55/1.00  fd_cond                                 0
% 3.55/1.00  fd_pseudo_cond                          1
% 3.55/1.00  AC symbols                              0
% 3.55/1.00  
% 3.55/1.00  ------ Schedule dynamic 5 is on 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  Current options:
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    --mode clausify
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         false
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     none
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       false
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.01  --demod_use_ground                      true
% 3.55/1.01  --sup_to_prop_solver                    passive
% 3.55/1.01  --sup_prop_simpl_new                    true
% 3.55/1.01  --sup_prop_simpl_given                  true
% 3.55/1.01  --sup_fun_splitting                     false
% 3.55/1.01  --sup_smt_interval                      50000
% 3.55/1.01  
% 3.55/1.01  ------ Superposition Simplification Setup
% 3.55/1.01  
% 3.55/1.01  --sup_indices_passive                   []
% 3.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.01  --sup_full_bw                           [BwDemod]
% 3.55/1.01  --sup_immed_triv                        [TrivRules]
% 3.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.01  --sup_immed_bw_main                     []
% 3.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/1.01  
% 3.55/1.01  ------ Combination Options
% 3.55/1.01  
% 3.55/1.01  --comb_res_mult                         3
% 3.55/1.01  --comb_sup_mult                         2
% 3.55/1.01  --comb_inst_mult                        10
% 3.55/1.01  
% 3.55/1.01  ------ Debug Options
% 3.55/1.01  
% 3.55/1.01  --dbg_backtrace                         false
% 3.55/1.01  --dbg_dump_prop_clauses                 false
% 3.55/1.01  --dbg_dump_prop_clauses_file            -
% 3.55/1.01  --dbg_out_stat                          false
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  ------ Proving...
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  % SZS status Theorem for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  fof(f1,axiom,(
% 3.55/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f14,plain,(
% 3.55/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.55/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 3.55/1.01  
% 3.55/1.01  fof(f15,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.55/1.01    inference(ennf_transformation,[],[f14])).
% 3.55/1.01  
% 3.55/1.01  fof(f37,plain,(
% 3.55/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f15])).
% 3.55/1.01  
% 3.55/1.01  fof(f2,axiom,(
% 3.55/1.01    v1_xboole_0(k1_xboole_0)),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f38,plain,(
% 3.55/1.01    v1_xboole_0(k1_xboole_0)),
% 3.55/1.01    inference(cnf_transformation,[],[f2])).
% 3.55/1.01  
% 3.55/1.01  fof(f11,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f24,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(ennf_transformation,[],[f11])).
% 3.55/1.01  
% 3.55/1.01  fof(f25,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(flattening,[],[f24])).
% 3.55/1.01  
% 3.55/1.01  fof(f34,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(nnf_transformation,[],[f25])).
% 3.55/1.01  
% 3.55/1.01  fof(f53,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f34])).
% 3.55/1.01  
% 3.55/1.01  fof(f12,conjecture,(
% 3.55/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f13,negated_conjecture,(
% 3.55/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.55/1.01    inference(negated_conjecture,[],[f12])).
% 3.55/1.01  
% 3.55/1.01  fof(f26,plain,(
% 3.55/1.01    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.55/1.01    inference(ennf_transformation,[],[f13])).
% 3.55/1.01  
% 3.55/1.01  fof(f27,plain,(
% 3.55/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.55/1.01    inference(flattening,[],[f26])).
% 3.55/1.01  
% 3.55/1.01  fof(f35,plain,(
% 3.55/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f36,plain,(
% 3.55/1.01    ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f35])).
% 3.55/1.01  
% 3.55/1.01  fof(f60,plain,(
% 3.55/1.01    v1_funct_2(sK4,sK2,sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f61,plain,(
% 3.55/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f9,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f22,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(ennf_transformation,[],[f9])).
% 3.55/1.01  
% 3.55/1.01  fof(f51,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f22])).
% 3.55/1.01  
% 3.55/1.01  fof(f10,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f23,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(ennf_transformation,[],[f10])).
% 3.55/1.01  
% 3.55/1.01  fof(f52,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f23])).
% 3.55/1.01  
% 3.55/1.01  fof(f62,plain,(
% 3.55/1.01    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f8,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f21,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.01    inference(ennf_transformation,[],[f8])).
% 3.55/1.01  
% 3.55/1.01  fof(f50,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f21])).
% 3.55/1.01  
% 3.55/1.01  fof(f5,axiom,(
% 3.55/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f18,plain,(
% 3.55/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.55/1.01    inference(ennf_transformation,[],[f5])).
% 3.55/1.01  
% 3.55/1.01  fof(f44,plain,(
% 3.55/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f18])).
% 3.55/1.01  
% 3.55/1.01  fof(f4,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f17,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(ennf_transformation,[],[f4])).
% 3.55/1.01  
% 3.55/1.01  fof(f28,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(nnf_transformation,[],[f17])).
% 3.55/1.01  
% 3.55/1.01  fof(f29,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(rectify,[],[f28])).
% 3.55/1.01  
% 3.55/1.01  fof(f30,plain,(
% 3.55/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f31,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.55/1.01  
% 3.55/1.01  fof(f41,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f31])).
% 3.55/1.01  
% 3.55/1.01  fof(f7,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f19,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.55/1.01    inference(ennf_transformation,[],[f7])).
% 3.55/1.01  
% 3.55/1.01  fof(f20,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(flattening,[],[f19])).
% 3.55/1.01  
% 3.55/1.01  fof(f32,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(nnf_transformation,[],[f20])).
% 3.55/1.01  
% 3.55/1.01  fof(f33,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.55/1.01    inference(flattening,[],[f32])).
% 3.55/1.01  
% 3.55/1.01  fof(f48,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f33])).
% 3.55/1.01  
% 3.55/1.01  fof(f59,plain,(
% 3.55/1.01    v1_funct_1(sK4)),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f63,plain,(
% 3.55/1.01    ( ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f40,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f31])).
% 3.55/1.01  
% 3.55/1.01  fof(f3,axiom,(
% 3.55/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f16,plain,(
% 3.55/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.55/1.01    inference(ennf_transformation,[],[f3])).
% 3.55/1.01  
% 3.55/1.01  fof(f39,plain,(
% 3.55/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f16])).
% 3.55/1.01  
% 3.55/1.01  fof(f57,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f34])).
% 3.55/1.01  
% 3.55/1.01  fof(f67,plain,(
% 3.55/1.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.55/1.01    inference(equality_resolution,[],[f57])).
% 3.55/1.01  
% 3.55/1.01  fof(f54,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f34])).
% 3.55/1.01  
% 3.55/1.01  fof(f69,plain,(
% 3.55/1.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.55/1.01    inference(equality_resolution,[],[f54])).
% 3.55/1.01  
% 3.55/1.01  fof(f6,axiom,(
% 3.55/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f46,plain,(
% 3.55/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.55/1.01    inference(cnf_transformation,[],[f6])).
% 3.55/1.01  
% 3.55/1.01  cnf(c_0,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1,plain,
% 3.55/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_291,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_292,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_291]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_12357,plain,
% 3.55/1.01      ( ~ r2_hidden(sK1,k1_xboole_0) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_292]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1508,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.55/1.01      theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_4748,plain,
% 3.55/1.01      ( m1_subset_1(X0,X1)
% 3.55/1.01      | ~ m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
% 3.55/1.01      | X0 != sK0(sK1,k1_relat_1(sK4),sK4)
% 3.55/1.01      | X1 != k1_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11352,plain,
% 3.55/1.01      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),X0)
% 3.55/1.01      | ~ m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
% 3.55/1.01      | X0 != k1_relat_1(sK4)
% 3.55/1.01      | sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_4748]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11353,plain,
% 3.55/1.01      ( X0 != k1_relat_1(sK4)
% 3.55/1.01      | sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4)
% 3.55/1.01      | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),X0) = iProver_top
% 3.55/1.01      | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_11352]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11355,plain,
% 3.55/1.01      ( sK0(sK1,k1_relat_1(sK4),sK4) != sK0(sK1,k1_relat_1(sK4),sK4)
% 3.55/1.01      | k1_xboole_0 != k1_relat_1(sK4)
% 3.55/1.01      | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top
% 3.55/1.01      | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_xboole_0) = iProver_top ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_11353]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_21,plain,
% 3.55/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.55/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.55/1.01      | k1_xboole_0 = X2 ),
% 3.55/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_25,negated_conjecture,
% 3.55/1.01      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_894,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.55/1.01      | sK3 != X2
% 3.55/1.01      | sK2 != X1
% 3.55/1.01      | sK4 != X0
% 3.55/1.01      | k1_xboole_0 = X2 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_895,plain,
% 3.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.55/1.01      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.55/1.01      | k1_xboole_0 = sK3 ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_894]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_24,negated_conjecture,
% 3.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.55/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_897,plain,
% 3.55/1.01      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_895,c_24]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1842,plain,
% 3.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_14,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1846,plain,
% 3.55/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.55/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2431,plain,
% 3.55/1.01      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1842,c_1846]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2704,plain,
% 3.55/1.01      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_897,c_2431]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_15,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1845,plain,
% 3.55/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.55/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2358,plain,
% 3.55/1.01      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1842,c_1845]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_23,negated_conjecture,
% 3.55/1.01      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
% 3.55/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1843,plain,
% 3.55/1.01      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2421,plain,
% 3.55/1.01      ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_2358,c_1843]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_13,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.01      | v1_relat_1(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1847,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.55/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2300,plain,
% 3.55/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1842,c_1847]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_7,plain,
% 3.55/1.01      ( ~ v1_relat_1(X0)
% 3.55/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1848,plain,
% 3.55/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.55/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2304,plain,
% 3.55/1.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2300,c_1848]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.55/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.55/1.01      | ~ v1_relat_1(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1850,plain,
% 3.55/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.55/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.55/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11,plain,
% 3.55/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.55/1.01      | ~ v1_funct_1(X2)
% 3.55/1.01      | ~ v1_relat_1(X2)
% 3.55/1.01      | k1_funct_1(X2,X0) = X1 ),
% 3.55/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_26,negated_conjecture,
% 3.55/1.01      ( v1_funct_1(sK4) ),
% 3.55/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_302,plain,
% 3.55/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.55/1.01      | ~ v1_relat_1(X2)
% 3.55/1.01      | k1_funct_1(X2,X0) = X1
% 3.55/1.01      | sK4 != X2 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_303,plain,
% 3.55/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 3.55/1.01      | ~ v1_relat_1(sK4)
% 3.55/1.01      | k1_funct_1(sK4,X0) = X1 ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_302]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1840,plain,
% 3.55/1.01      ( k1_funct_1(sK4,X0) = X1
% 3.55/1.01      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 3.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_29,plain,
% 3.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_304,plain,
% 3.55/1.01      ( k1_funct_1(sK4,X0) = X1
% 3.55/1.01      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 3.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1998,plain,
% 3.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.55/1.01      | v1_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1999,plain,
% 3.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.55/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2025,plain,
% 3.55/1.01      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 3.55/1.01      | k1_funct_1(sK4,X0) = X1 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_1840,c_29,c_304,c_1999]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2026,plain,
% 3.55/1.01      ( k1_funct_1(sK4,X0) = X1
% 3.55/1.01      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 3.55/1.01      inference(renaming,[status(thm)],[c_2025]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2611,plain,
% 3.55/1.01      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1850,c_2026]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2831,plain,
% 3.55/1.01      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.55/1.01      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_2611,c_29,c_1999]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2832,plain,
% 3.55/1.01      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 3.55/1.01      inference(renaming,[status(thm)],[c_2831]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2841,plain,
% 3.55/1.01      ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
% 3.55/1.01      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2304,c_2832]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2965,plain,
% 3.55/1.01      ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2421,c_2841]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_22,negated_conjecture,
% 3.55/1.01      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) != sK1 ),
% 3.55/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1844,plain,
% 3.55/1.01      ( k1_funct_1(sK4,X0) != sK1 | m1_subset_1(X0,sK2) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3206,plain,
% 3.55/1.01      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2965,c_1844]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3258,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2704,c_3206]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_30,plain,
% 3.55/1.01      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2011,plain,
% 3.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.55/1.01      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1505,plain,( X0 = X0 ),theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2089,plain,
% 3.55/1.01      ( sK1 = sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1506,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2122,plain,
% 3.55/1.01      ( X0 != X1
% 3.55/1.01      | X0 = k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | k2_relset_1(sK2,sK3,sK4) != X1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2214,plain,
% 3.55/1.01      ( X0 = k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | X0 != k2_relat_1(sK4)
% 3.55/1.01      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2122]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2243,plain,
% 3.55/1.01      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.55/1.01      | k2_relat_1(sK4) = k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | k2_relat_1(sK4) != k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2214]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2244,plain,
% 3.55/1.01      ( k2_relat_1(sK4) = k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1507,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.55/1.01      theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2014,plain,
% 3.55/1.01      ( r2_hidden(X0,X1)
% 3.55/1.01      | ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
% 3.55/1.01      | X1 != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | X0 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1507]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2088,plain,
% 3.55/1.01      ( r2_hidden(sK1,X0)
% 3.55/1.01      | ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
% 3.55/1.01      | X0 != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | sK1 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2014]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2371,plain,
% 3.55/1.01      ( ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
% 3.55/1.01      | r2_hidden(sK1,k2_relat_1(sK4))
% 3.55/1.01      | k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | sK1 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2372,plain,
% 3.55/1.01      ( k2_relat_1(sK4) != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | sK1 != sK1
% 3.55/1.01      | r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 3.55/1.01      | r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.55/1.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.55/1.01      | ~ v1_relat_1(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1849,plain,
% 3.55/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.55/1.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.55/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2752,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.55/1.01      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 3.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2704,c_1849]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2947,plain,
% 3.55/1.01      ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.55/1.01      | sK3 = k1_xboole_0 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_2752,c_29,c_1999]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2948,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.55/1.01      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
% 3.55/1.01      inference(renaming,[status(thm)],[c_2947]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2,plain,
% 3.55/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1853,plain,
% 3.55/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.55/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2956,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
% 3.55/1.01      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2948,c_1853]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3257,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_2956,c_3206]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3265,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0
% 3.55/1.01      | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_3257,c_2304]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3271,plain,
% 3.55/1.01      ( sK3 = k1_xboole_0 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_3258,c_24,c_30,c_2011,c_2089,c_2243,c_2244,c_2372,
% 3.55/1.01                 c_3265]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_17,plain,
% 3.55/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.55/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.55/1.01      | k1_xboole_0 = X1
% 3.55/1.01      | k1_xboole_0 = X0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_861,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.55/1.01      | sK3 != k1_xboole_0
% 3.55/1.01      | sK2 != X1
% 3.55/1.01      | sK4 != X0
% 3.55/1.01      | k1_xboole_0 = X1
% 3.55/1.01      | k1_xboole_0 = X0 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_862,plain,
% 3.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.55/1.01      | sK3 != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = sK2
% 3.55/1.01      | k1_xboole_0 = sK4 ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_861]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1837,plain,
% 3.55/1.01      ( sK3 != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = sK2
% 3.55/1.01      | k1_xboole_0 = sK4
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3276,plain,
% 3.55/1.01      ( sK2 = k1_xboole_0
% 3.55/1.01      | sK4 = k1_xboole_0
% 3.55/1.01      | k1_xboole_0 != k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_3271,c_1837]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3288,plain,
% 3.55/1.01      ( sK2 = k1_xboole_0
% 3.55/1.01      | sK4 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_3276]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3279,plain,
% 3.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_3271,c_1842]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3292,plain,
% 3.55/1.01      ( sK2 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.55/1.01      inference(forward_subsumption_resolution,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_3288,c_3279]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_20,plain,
% 3.55/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.55/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.55/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_881,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.55/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.55/1.01      | sK3 != X1
% 3.55/1.01      | sK2 != k1_xboole_0
% 3.55/1.01      | sK4 != X0 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_882,plain,
% 3.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.55/1.01      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 3.55/1.01      | sK2 != k1_xboole_0 ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_881]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1836,plain,
% 3.55/1.01      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 3.55/1.01      | sK2 != k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3277,plain,
% 3.55/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.55/1.01      | sK2 != k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_3271,c_1836]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3972,plain,
% 3.55/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.55/1.01      | sK4 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3292,c_3277]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3975,plain,
% 3.55/1.01      ( sK4 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3292,c_3279]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3997,plain,
% 3.55/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.55/1.01      | sK4 = k1_xboole_0 ),
% 3.55/1.01      inference(forward_subsumption_resolution,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_3972,c_3975]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3274,plain,
% 3.55/1.01      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_3271,c_2431]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3974,plain,
% 3.55/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
% 3.55/1.01      | sK4 = k1_xboole_0 ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3292,c_3274]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6327,plain,
% 3.55/1.01      ( k1_relat_1(sK4) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3997,c_3974]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6307,plain,
% 3.55/1.01      ( sK0(sK1,k1_relat_1(sK4),sK4) = sK0(sK1,k1_relat_1(sK4),sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5886,plain,
% 3.55/1.01      ( X0 != X1 | X0 = k1_relat_1(sK4) | k1_relat_1(sK4) != X1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5887,plain,
% 3.55/1.01      ( k1_relat_1(sK4) != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = k1_relat_1(sK4)
% 3.55/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_5886]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5782,plain,
% 3.55/1.01      ( X0 != X1 | X0 = k2_relat_1(X2) | k2_relat_1(X2) != X1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5783,plain,
% 3.55/1.01      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.55/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_5782]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3976,plain,
% 3.55/1.01      ( sK4 = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_xboole_0) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3292,c_3206]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2565,plain,
% 3.55/1.01      ( r2_hidden(X0,X1)
% 3.55/1.01      | ~ r2_hidden(sK1,k2_relat_1(sK4))
% 3.55/1.01      | X1 != k2_relat_1(sK4)
% 3.55/1.01      | X0 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1507]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3345,plain,
% 3.55/1.01      ( r2_hidden(sK1,X0)
% 3.55/1.01      | ~ r2_hidden(sK1,k2_relat_1(sK4))
% 3.55/1.01      | X0 != k2_relat_1(sK4)
% 3.55/1.01      | sK1 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2565]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3347,plain,
% 3.55/1.01      ( ~ r2_hidden(sK1,k2_relat_1(sK4))
% 3.55/1.01      | r2_hidden(sK1,k1_xboole_0)
% 3.55/1.01      | sK1 != sK1
% 3.55/1.01      | k1_xboole_0 != k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_3345]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3017,plain,
% 3.55/1.01      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
% 3.55/1.01      | ~ r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3018,plain,
% 3.55/1.01      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) = iProver_top
% 3.55/1.01      | r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_3017]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2046,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.55/1.01      | r2_hidden(sK0(X0,X1,sK4),k1_relat_1(sK4))
% 3.55/1.01      | ~ v1_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2583,plain,
% 3.55/1.01      ( r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4))
% 3.55/1.01      | ~ r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4)))
% 3.55/1.01      | ~ v1_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2046]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2584,plain,
% 3.55/1.01      ( r2_hidden(sK0(sK1,k1_relat_1(sK4),sK4),k1_relat_1(sK4)) = iProver_top
% 3.55/1.01      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top
% 3.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1513,plain,
% 3.55/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.55/1.01      theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2400,plain,
% 3.55/1.01      ( k2_relat_1(sK4) = k2_relat_1(X0) | sK4 != X0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2402,plain,
% 3.55/1.01      ( k2_relat_1(sK4) = k2_relat_1(k1_xboole_0) | sK4 != k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2400]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2245,plain,
% 3.55/1.01      ( X0 != X1 | X0 = k2_relat_1(sK4) | k2_relat_1(sK4) != X1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2399,plain,
% 3.55/1.01      ( X0 != k2_relat_1(X1)
% 3.55/1.01      | X0 = k2_relat_1(sK4)
% 3.55/1.01      | k2_relat_1(sK4) != k2_relat_1(X1) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2245]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2401,plain,
% 3.55/1.01      ( k2_relat_1(sK4) != k2_relat_1(k1_xboole_0)
% 3.55/1.01      | k1_xboole_0 = k2_relat_1(sK4)
% 3.55/1.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2399]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2379,plain,
% 3.55/1.01      ( ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
% 3.55/1.01      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4)))
% 3.55/1.01      | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | sK1 != sK1 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2380,plain,
% 3.55/1.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | sK1 != sK1
% 3.55/1.01      | r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 3.55/1.01      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2379]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2252,plain,
% 3.55/1.01      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.55/1.01      | k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relset_1(sK2,sK3,sK4)
% 3.55/1.01      | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2214]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2061,plain,
% 3.55/1.01      ( ~ v1_relat_1(sK4)
% 3.55/1.01      | k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1532,plain,
% 3.55/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_8,plain,
% 3.55/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(contradiction,plain,
% 3.55/1.01      ( $false ),
% 3.55/1.01      inference(minisat,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_12357,c_11355,c_6327,c_6307,c_5887,c_5783,c_3976,
% 3.55/1.01                 c_3347,c_3018,c_2584,c_2402,c_2401,c_2380,c_2371,c_2252,
% 3.55/1.01                 c_2244,c_2243,c_2089,c_2061,c_2011,c_1999,c_1998,c_1532,
% 3.55/1.01                 c_8,c_30,c_23,c_29,c_24]) ).
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  ------                               Statistics
% 3.55/1.01  
% 3.55/1.01  ------ General
% 3.55/1.01  
% 3.55/1.01  abstr_ref_over_cycles:                  0
% 3.55/1.01  abstr_ref_under_cycles:                 0
% 3.55/1.01  gc_basic_clause_elim:                   0
% 3.55/1.01  forced_gc_time:                         0
% 3.55/1.01  parsing_time:                           0.013
% 3.55/1.01  unif_index_cands_time:                  0.
% 3.55/1.01  unif_index_add_time:                    0.
% 3.55/1.01  orderings_time:                         0.
% 3.55/1.01  out_proof_time:                         0.011
% 3.55/1.01  total_time:                             0.361
% 3.55/1.01  num_of_symbols:                         52
% 3.55/1.01  num_of_terms:                           8503
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing
% 3.55/1.01  
% 3.55/1.01  num_of_splits:                          0
% 3.55/1.01  num_of_split_atoms:                     0
% 3.55/1.01  num_of_reused_defs:                     0
% 3.55/1.01  num_eq_ax_congr_red:                    18
% 3.55/1.01  num_of_sem_filtered_clauses:            1
% 3.55/1.01  num_of_subtypes:                        0
% 3.55/1.01  monotx_restored_types:                  0
% 3.55/1.01  sat_num_of_epr_types:                   0
% 3.55/1.01  sat_num_of_non_cyclic_types:            0
% 3.55/1.01  sat_guarded_non_collapsed_types:        0
% 3.55/1.01  num_pure_diseq_elim:                    0
% 3.55/1.01  simp_replaced_by:                       0
% 3.55/1.01  res_preprocessed:                       119
% 3.55/1.01  prep_upred:                             0
% 3.55/1.01  prep_unflattend:                        106
% 3.55/1.01  smt_new_axioms:                         0
% 3.55/1.01  pred_elim_cands:                        3
% 3.55/1.01  pred_elim:                              3
% 3.55/1.01  pred_elim_cl:                           6
% 3.55/1.01  pred_elim_cycles:                       8
% 3.55/1.01  merged_defs:                            0
% 3.55/1.01  merged_defs_ncl:                        0
% 3.55/1.01  bin_hyper_res:                          0
% 3.55/1.01  prep_cycles:                            4
% 3.55/1.01  pred_elim_time:                         0.018
% 3.55/1.01  splitting_time:                         0.
% 3.55/1.01  sem_filter_time:                        0.
% 3.55/1.01  monotx_time:                            0.
% 3.55/1.01  subtype_inf_time:                       0.
% 3.55/1.01  
% 3.55/1.01  ------ Problem properties
% 3.55/1.01  
% 3.55/1.01  clauses:                                21
% 3.55/1.01  conjectures:                            3
% 3.55/1.01  epr:                                    2
% 3.55/1.01  horn:                                   19
% 3.55/1.01  ground:                                 7
% 3.55/1.01  unary:                                  5
% 3.55/1.01  binary:                                 7
% 3.55/1.01  lits:                                   49
% 3.55/1.01  lits_eq:                                14
% 3.55/1.01  fd_pure:                                0
% 3.55/1.01  fd_pseudo:                              0
% 3.55/1.01  fd_cond:                                0
% 3.55/1.01  fd_pseudo_cond:                         1
% 3.55/1.01  ac_symbols:                             0
% 3.55/1.01  
% 3.55/1.01  ------ Propositional Solver
% 3.55/1.01  
% 3.55/1.01  prop_solver_calls:                      34
% 3.55/1.01  prop_fast_solver_calls:                 1420
% 3.55/1.01  smt_solver_calls:                       0
% 3.55/1.01  smt_fast_solver_calls:                  0
% 3.55/1.01  prop_num_of_clauses:                    3465
% 3.55/1.01  prop_preprocess_simplified:             6480
% 3.55/1.01  prop_fo_subsumed:                       40
% 3.55/1.01  prop_solver_time:                       0.
% 3.55/1.01  smt_solver_time:                        0.
% 3.55/1.01  smt_fast_solver_time:                   0.
% 3.55/1.01  prop_fast_solver_time:                  0.
% 3.55/1.01  prop_unsat_core_time:                   0.
% 3.55/1.01  
% 3.55/1.01  ------ QBF
% 3.55/1.01  
% 3.55/1.01  qbf_q_res:                              0
% 3.55/1.01  qbf_num_tautologies:                    0
% 3.55/1.01  qbf_prep_cycles:                        0
% 3.55/1.01  
% 3.55/1.01  ------ BMC1
% 3.55/1.01  
% 3.55/1.01  bmc1_current_bound:                     -1
% 3.55/1.01  bmc1_last_solved_bound:                 -1
% 3.55/1.01  bmc1_unsat_core_size:                   -1
% 3.55/1.01  bmc1_unsat_core_parents_size:           -1
% 3.55/1.01  bmc1_merge_next_fun:                    0
% 3.55/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.01  
% 3.55/1.01  ------ Instantiation
% 3.55/1.01  
% 3.55/1.01  inst_num_of_clauses:                    1061
% 3.55/1.01  inst_num_in_passive:                    413
% 3.55/1.01  inst_num_in_active:                     625
% 3.55/1.01  inst_num_in_unprocessed:                22
% 3.55/1.01  inst_num_of_loops:                      835
% 3.55/1.01  inst_num_of_learning_restarts:          0
% 3.55/1.01  inst_num_moves_active_passive:          200
% 3.55/1.01  inst_lit_activity:                      0
% 3.55/1.01  inst_lit_activity_moves:                0
% 3.55/1.01  inst_num_tautologies:                   0
% 3.55/1.01  inst_num_prop_implied:                  0
% 3.55/1.01  inst_num_existing_simplified:           0
% 3.55/1.01  inst_num_eq_res_simplified:             0
% 3.55/1.01  inst_num_child_elim:                    0
% 3.55/1.01  inst_num_of_dismatching_blockings:      188
% 3.55/1.01  inst_num_of_non_proper_insts:           1160
% 3.55/1.01  inst_num_of_duplicates:                 0
% 3.55/1.01  inst_inst_num_from_inst_to_res:         0
% 3.55/1.01  inst_dismatching_checking_time:         0.
% 3.55/1.01  
% 3.55/1.01  ------ Resolution
% 3.55/1.01  
% 3.55/1.01  res_num_of_clauses:                     0
% 3.55/1.01  res_num_in_passive:                     0
% 3.55/1.01  res_num_in_active:                      0
% 3.55/1.01  res_num_of_loops:                       123
% 3.55/1.01  res_forward_subset_subsumed:            180
% 3.55/1.01  res_backward_subset_subsumed:           4
% 3.55/1.01  res_forward_subsumed:                   0
% 3.55/1.01  res_backward_subsumed:                  0
% 3.55/1.01  res_forward_subsumption_resolution:     0
% 3.55/1.01  res_backward_subsumption_resolution:    0
% 3.55/1.01  res_clause_to_clause_subsumption:       1626
% 3.55/1.01  res_orphan_elimination:                 0
% 3.55/1.01  res_tautology_del:                      261
% 3.55/1.01  res_num_eq_res_simplified:              0
% 3.55/1.01  res_num_sel_changes:                    0
% 3.55/1.01  res_moves_from_active_to_pass:          0
% 3.55/1.01  
% 3.55/1.01  ------ Superposition
% 3.55/1.01  
% 3.55/1.01  sup_time_total:                         0.
% 3.55/1.01  sup_time_generating:                    0.
% 3.55/1.01  sup_time_sim_full:                      0.
% 3.55/1.01  sup_time_sim_immed:                     0.
% 3.55/1.01  
% 3.55/1.01  sup_num_of_clauses:                     312
% 3.55/1.01  sup_num_in_active:                      156
% 3.55/1.01  sup_num_in_passive:                     156
% 3.55/1.01  sup_num_of_loops:                       166
% 3.55/1.01  sup_fw_superposition:                   335
% 3.55/1.01  sup_bw_superposition:                   200
% 3.55/1.01  sup_immediate_simplified:               176
% 3.55/1.01  sup_given_eliminated:                   0
% 3.55/1.01  comparisons_done:                       0
% 3.55/1.01  comparisons_avoided:                    12
% 3.55/1.01  
% 3.55/1.01  ------ Simplifications
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  sim_fw_subset_subsumed:                 85
% 3.55/1.01  sim_bw_subset_subsumed:                 11
% 3.55/1.01  sim_fw_subsumed:                        54
% 3.55/1.01  sim_bw_subsumed:                        4
% 3.55/1.01  sim_fw_subsumption_res:                 4
% 3.55/1.01  sim_bw_subsumption_res:                 0
% 3.55/1.01  sim_tautology_del:                      7
% 3.55/1.01  sim_eq_tautology_del:                   5
% 3.55/1.01  sim_eq_res_simp:                        1
% 3.55/1.01  sim_fw_demodulated:                     0
% 3.55/1.01  sim_bw_demodulated:                     8
% 3.55/1.01  sim_light_normalised:                   54
% 3.55/1.01  sim_joinable_taut:                      0
% 3.55/1.01  sim_joinable_simp:                      0
% 3.55/1.01  sim_ac_normalised:                      0
% 3.55/1.01  sim_smt_subsumption:                    0
% 3.55/1.01  
%------------------------------------------------------------------------------
