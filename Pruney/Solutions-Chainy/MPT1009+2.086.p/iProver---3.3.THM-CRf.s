%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:45 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 837 expanded)
%              Number of clauses        :   75 ( 229 expanded)
%              Number of leaves         :   15 ( 191 expanded)
%              Depth                    :   20
%              Number of atoms          :  350 (2447 expanded)
%              Number of equality atoms :  195 ( 955 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).

fof(f53,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f66,plain,(
    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f53,f57])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f55,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f60])).

fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f56,f57,f57])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_422,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_737,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_422])).

cnf(c_738,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_739,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_18])).

cnf(c_740,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_796,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_740])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_466,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_467,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1314,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_467])).

cnf(c_1378,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_796,c_1314])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1202,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1440,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_1202])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_475,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_476,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_587,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_476,c_264])).

cnf(c_938,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_587])).

cnf(c_1198,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_939,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_587])).

cnf(c_981,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_982,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_941,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1315,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_622,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_476])).

cnf(c_623,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_933,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_623])).

cnf(c_1316,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1321,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_2526,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_981,c_982,c_1315,c_1321])).

cnf(c_2527,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2526])).

cnf(c_2536,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1440,c_2527])).

cnf(c_934,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_623])).

cnf(c_1192,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_935,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_623])).

cnf(c_1951,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_935,c_934,c_1315,c_1316])).

cnf(c_1955,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1378,c_1951])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_601,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_476])).

cnf(c_602,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_1317,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1435,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_1315,c_1317])).

cnf(c_1960,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_1955,c_1435])).

cnf(c_2538,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2536,c_1960])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1200,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1383,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1378,c_1200])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_457,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_458,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1329,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_458])).

cnf(c_1550,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_1329,c_1378])).

cnf(c_1690,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1383,c_1550])).

cnf(c_3881,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2538,c_1690])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_610,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_476])).

cnf(c_611,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_936,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_611])).

cnf(c_1195,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_937,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_611])).

cnf(c_976,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_977,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1876,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_976,c_977,c_1315,c_1321])).

cnf(c_4164,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3881,c_1876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.44/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.01  
% 2.44/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.01  
% 2.44/1.01  ------  iProver source info
% 2.44/1.01  
% 2.44/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.01  git: non_committed_changes: false
% 2.44/1.01  git: last_make_outside_of_git: false
% 2.44/1.01  
% 2.44/1.01  ------ 
% 2.44/1.01  
% 2.44/1.01  ------ Input Options
% 2.44/1.01  
% 2.44/1.01  --out_options                           all
% 2.44/1.01  --tptp_safe_out                         true
% 2.44/1.01  --problem_path                          ""
% 2.44/1.01  --include_path                          ""
% 2.44/1.01  --clausifier                            res/vclausify_rel
% 2.44/1.01  --clausifier_options                    --mode clausify
% 2.44/1.01  --stdin                                 false
% 2.44/1.01  --stats_out                             all
% 2.44/1.01  
% 2.44/1.01  ------ General Options
% 2.44/1.01  
% 2.44/1.01  --fof                                   false
% 2.44/1.01  --time_out_real                         305.
% 2.44/1.01  --time_out_virtual                      -1.
% 2.44/1.01  --symbol_type_check                     false
% 2.44/1.01  --clausify_out                          false
% 2.44/1.01  --sig_cnt_out                           false
% 2.44/1.01  --trig_cnt_out                          false
% 2.44/1.01  --trig_cnt_out_tolerance                1.
% 2.44/1.01  --trig_cnt_out_sk_spl                   false
% 2.44/1.01  --abstr_cl_out                          false
% 2.44/1.01  
% 2.44/1.01  ------ Global Options
% 2.44/1.01  
% 2.44/1.01  --schedule                              default
% 2.44/1.01  --add_important_lit                     false
% 2.44/1.01  --prop_solver_per_cl                    1000
% 2.44/1.01  --min_unsat_core                        false
% 2.44/1.01  --soft_assumptions                      false
% 2.44/1.01  --soft_lemma_size                       3
% 2.44/1.01  --prop_impl_unit_size                   0
% 2.44/1.01  --prop_impl_unit                        []
% 2.44/1.01  --share_sel_clauses                     true
% 2.44/1.01  --reset_solvers                         false
% 2.44/1.01  --bc_imp_inh                            [conj_cone]
% 2.44/1.01  --conj_cone_tolerance                   3.
% 2.44/1.01  --extra_neg_conj                        none
% 2.44/1.01  --large_theory_mode                     true
% 2.44/1.01  --prolific_symb_bound                   200
% 2.44/1.01  --lt_threshold                          2000
% 2.44/1.01  --clause_weak_htbl                      true
% 2.44/1.01  --gc_record_bc_elim                     false
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing Options
% 2.44/1.01  
% 2.44/1.01  --preprocessing_flag                    true
% 2.44/1.01  --time_out_prep_mult                    0.1
% 2.44/1.01  --splitting_mode                        input
% 2.44/1.01  --splitting_grd                         true
% 2.44/1.01  --splitting_cvd                         false
% 2.44/1.01  --splitting_cvd_svl                     false
% 2.44/1.01  --splitting_nvd                         32
% 2.44/1.01  --sub_typing                            true
% 2.44/1.01  --prep_gs_sim                           true
% 2.44/1.01  --prep_unflatten                        true
% 2.44/1.01  --prep_res_sim                          true
% 2.44/1.01  --prep_upred                            true
% 2.44/1.01  --prep_sem_filter                       exhaustive
% 2.44/1.01  --prep_sem_filter_out                   false
% 2.44/1.01  --pred_elim                             true
% 2.44/1.01  --res_sim_input                         true
% 2.44/1.01  --eq_ax_congr_red                       true
% 2.44/1.01  --pure_diseq_elim                       true
% 2.44/1.01  --brand_transform                       false
% 2.44/1.01  --non_eq_to_eq                          false
% 2.44/1.01  --prep_def_merge                        true
% 2.44/1.01  --prep_def_merge_prop_impl              false
% 2.44/1.01  --prep_def_merge_mbd                    true
% 2.44/1.01  --prep_def_merge_tr_red                 false
% 2.44/1.01  --prep_def_merge_tr_cl                  false
% 2.44/1.01  --smt_preprocessing                     true
% 2.44/1.01  --smt_ac_axioms                         fast
% 2.44/1.01  --preprocessed_out                      false
% 2.44/1.01  --preprocessed_stats                    false
% 2.44/1.01  
% 2.44/1.01  ------ Abstraction refinement Options
% 2.44/1.01  
% 2.44/1.01  --abstr_ref                             []
% 2.44/1.01  --abstr_ref_prep                        false
% 2.44/1.01  --abstr_ref_until_sat                   false
% 2.44/1.01  --abstr_ref_sig_restrict                funpre
% 2.44/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.01  --abstr_ref_under                       []
% 2.44/1.01  
% 2.44/1.01  ------ SAT Options
% 2.44/1.01  
% 2.44/1.01  --sat_mode                              false
% 2.44/1.01  --sat_fm_restart_options                ""
% 2.44/1.01  --sat_gr_def                            false
% 2.44/1.01  --sat_epr_types                         true
% 2.44/1.01  --sat_non_cyclic_types                  false
% 2.44/1.01  --sat_finite_models                     false
% 2.44/1.01  --sat_fm_lemmas                         false
% 2.44/1.01  --sat_fm_prep                           false
% 2.44/1.01  --sat_fm_uc_incr                        true
% 2.44/1.01  --sat_out_model                         small
% 2.44/1.01  --sat_out_clauses                       false
% 2.44/1.01  
% 2.44/1.01  ------ QBF Options
% 2.44/1.01  
% 2.44/1.01  --qbf_mode                              false
% 2.44/1.01  --qbf_elim_univ                         false
% 2.44/1.01  --qbf_dom_inst                          none
% 2.44/1.01  --qbf_dom_pre_inst                      false
% 2.44/1.01  --qbf_sk_in                             false
% 2.44/1.01  --qbf_pred_elim                         true
% 2.44/1.01  --qbf_split                             512
% 2.44/1.01  
% 2.44/1.01  ------ BMC1 Options
% 2.44/1.01  
% 2.44/1.01  --bmc1_incremental                      false
% 2.44/1.01  --bmc1_axioms                           reachable_all
% 2.44/1.01  --bmc1_min_bound                        0
% 2.44/1.01  --bmc1_max_bound                        -1
% 2.44/1.01  --bmc1_max_bound_default                -1
% 2.44/1.01  --bmc1_symbol_reachability              true
% 2.44/1.01  --bmc1_property_lemmas                  false
% 2.44/1.01  --bmc1_k_induction                      false
% 2.44/1.01  --bmc1_non_equiv_states                 false
% 2.44/1.01  --bmc1_deadlock                         false
% 2.44/1.01  --bmc1_ucm                              false
% 2.44/1.01  --bmc1_add_unsat_core                   none
% 2.44/1.01  --bmc1_unsat_core_children              false
% 2.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.01  --bmc1_out_stat                         full
% 2.44/1.01  --bmc1_ground_init                      false
% 2.44/1.01  --bmc1_pre_inst_next_state              false
% 2.44/1.01  --bmc1_pre_inst_state                   false
% 2.44/1.01  --bmc1_pre_inst_reach_state             false
% 2.44/1.01  --bmc1_out_unsat_core                   false
% 2.44/1.01  --bmc1_aig_witness_out                  false
% 2.44/1.01  --bmc1_verbose                          false
% 2.44/1.01  --bmc1_dump_clauses_tptp                false
% 2.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.01  --bmc1_dump_file                        -
% 2.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.01  --bmc1_ucm_extend_mode                  1
% 2.44/1.01  --bmc1_ucm_init_mode                    2
% 2.44/1.01  --bmc1_ucm_cone_mode                    none
% 2.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.01  --bmc1_ucm_relax_model                  4
% 2.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.01  --bmc1_ucm_layered_model                none
% 2.44/1.01  --bmc1_ucm_max_lemma_size               10
% 2.44/1.01  
% 2.44/1.01  ------ AIG Options
% 2.44/1.01  
% 2.44/1.01  --aig_mode                              false
% 2.44/1.01  
% 2.44/1.01  ------ Instantiation Options
% 2.44/1.01  
% 2.44/1.01  --instantiation_flag                    true
% 2.44/1.01  --inst_sos_flag                         false
% 2.44/1.01  --inst_sos_phase                        true
% 2.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel_side                     num_symb
% 2.44/1.01  --inst_solver_per_active                1400
% 2.44/1.01  --inst_solver_calls_frac                1.
% 2.44/1.01  --inst_passive_queue_type               priority_queues
% 2.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.01  --inst_passive_queues_freq              [25;2]
% 2.44/1.01  --inst_dismatching                      true
% 2.44/1.01  --inst_eager_unprocessed_to_passive     true
% 2.44/1.01  --inst_prop_sim_given                   true
% 2.44/1.01  --inst_prop_sim_new                     false
% 2.44/1.01  --inst_subs_new                         false
% 2.44/1.01  --inst_eq_res_simp                      false
% 2.44/1.01  --inst_subs_given                       false
% 2.44/1.01  --inst_orphan_elimination               true
% 2.44/1.01  --inst_learning_loop_flag               true
% 2.44/1.01  --inst_learning_start                   3000
% 2.44/1.01  --inst_learning_factor                  2
% 2.44/1.01  --inst_start_prop_sim_after_learn       3
% 2.44/1.01  --inst_sel_renew                        solver
% 2.44/1.01  --inst_lit_activity_flag                true
% 2.44/1.01  --inst_restr_to_given                   false
% 2.44/1.01  --inst_activity_threshold               500
% 2.44/1.01  --inst_out_proof                        true
% 2.44/1.01  
% 2.44/1.01  ------ Resolution Options
% 2.44/1.01  
% 2.44/1.01  --resolution_flag                       true
% 2.44/1.01  --res_lit_sel                           adaptive
% 2.44/1.01  --res_lit_sel_side                      none
% 2.44/1.01  --res_ordering                          kbo
% 2.44/1.01  --res_to_prop_solver                    active
% 2.44/1.01  --res_prop_simpl_new                    false
% 2.44/1.01  --res_prop_simpl_given                  true
% 2.44/1.01  --res_passive_queue_type                priority_queues
% 2.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.01  --res_passive_queues_freq               [15;5]
% 2.44/1.01  --res_forward_subs                      full
% 2.44/1.01  --res_backward_subs                     full
% 2.44/1.01  --res_forward_subs_resolution           true
% 2.44/1.01  --res_backward_subs_resolution          true
% 2.44/1.01  --res_orphan_elimination                true
% 2.44/1.01  --res_time_limit                        2.
% 2.44/1.01  --res_out_proof                         true
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Options
% 2.44/1.01  
% 2.44/1.01  --superposition_flag                    true
% 2.44/1.01  --sup_passive_queue_type                priority_queues
% 2.44/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.01  --demod_completeness_check              fast
% 2.44/1.01  --demod_use_ground                      true
% 2.44/1.01  --sup_to_prop_solver                    passive
% 2.44/1.01  --sup_prop_simpl_new                    true
% 2.44/1.01  --sup_prop_simpl_given                  true
% 2.44/1.01  --sup_fun_splitting                     false
% 2.44/1.01  --sup_smt_interval                      50000
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Simplification Setup
% 2.44/1.01  
% 2.44/1.01  --sup_indices_passive                   []
% 2.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_full_bw                           [BwDemod]
% 2.44/1.01  --sup_immed_triv                        [TrivRules]
% 2.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_immed_bw_main                     []
% 2.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  
% 2.44/1.01  ------ Combination Options
% 2.44/1.01  
% 2.44/1.01  --comb_res_mult                         3
% 2.44/1.01  --comb_sup_mult                         2
% 2.44/1.01  --comb_inst_mult                        10
% 2.44/1.01  
% 2.44/1.01  ------ Debug Options
% 2.44/1.01  
% 2.44/1.01  --dbg_backtrace                         false
% 2.44/1.01  --dbg_dump_prop_clauses                 false
% 2.44/1.01  --dbg_dump_prop_clauses_file            -
% 2.44/1.01  --dbg_out_stat                          false
% 2.44/1.01  ------ Parsing...
% 2.44/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.01  ------ Proving...
% 2.44/1.01  ------ Problem Properties 
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  clauses                                 21
% 2.44/1.01  conjectures                             2
% 2.44/1.01  EPR                                     4
% 2.44/1.01  Horn                                    16
% 2.44/1.01  unary                                   4
% 2.44/1.01  binary                                  12
% 2.44/1.01  lits                                    44
% 2.44/1.01  lits eq                                 25
% 2.44/1.01  fd_pure                                 0
% 2.44/1.01  fd_pseudo                               0
% 2.44/1.01  fd_cond                                 0
% 2.44/1.01  fd_pseudo_cond                          2
% 2.44/1.01  AC symbols                              0
% 2.44/1.01  
% 2.44/1.01  ------ Schedule dynamic 5 is on 
% 2.44/1.01  
% 2.44/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  ------ 
% 2.44/1.01  Current options:
% 2.44/1.01  ------ 
% 2.44/1.01  
% 2.44/1.01  ------ Input Options
% 2.44/1.01  
% 2.44/1.01  --out_options                           all
% 2.44/1.01  --tptp_safe_out                         true
% 2.44/1.01  --problem_path                          ""
% 2.44/1.01  --include_path                          ""
% 2.44/1.01  --clausifier                            res/vclausify_rel
% 2.44/1.01  --clausifier_options                    --mode clausify
% 2.44/1.01  --stdin                                 false
% 2.44/1.01  --stats_out                             all
% 2.44/1.01  
% 2.44/1.01  ------ General Options
% 2.44/1.01  
% 2.44/1.01  --fof                                   false
% 2.44/1.01  --time_out_real                         305.
% 2.44/1.01  --time_out_virtual                      -1.
% 2.44/1.01  --symbol_type_check                     false
% 2.44/1.01  --clausify_out                          false
% 2.44/1.01  --sig_cnt_out                           false
% 2.44/1.01  --trig_cnt_out                          false
% 2.44/1.01  --trig_cnt_out_tolerance                1.
% 2.44/1.01  --trig_cnt_out_sk_spl                   false
% 2.44/1.01  --abstr_cl_out                          false
% 2.44/1.01  
% 2.44/1.01  ------ Global Options
% 2.44/1.01  
% 2.44/1.01  --schedule                              default
% 2.44/1.01  --add_important_lit                     false
% 2.44/1.01  --prop_solver_per_cl                    1000
% 2.44/1.01  --min_unsat_core                        false
% 2.44/1.01  --soft_assumptions                      false
% 2.44/1.01  --soft_lemma_size                       3
% 2.44/1.01  --prop_impl_unit_size                   0
% 2.44/1.01  --prop_impl_unit                        []
% 2.44/1.01  --share_sel_clauses                     true
% 2.44/1.01  --reset_solvers                         false
% 2.44/1.01  --bc_imp_inh                            [conj_cone]
% 2.44/1.01  --conj_cone_tolerance                   3.
% 2.44/1.01  --extra_neg_conj                        none
% 2.44/1.01  --large_theory_mode                     true
% 2.44/1.01  --prolific_symb_bound                   200
% 2.44/1.01  --lt_threshold                          2000
% 2.44/1.01  --clause_weak_htbl                      true
% 2.44/1.01  --gc_record_bc_elim                     false
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing Options
% 2.44/1.01  
% 2.44/1.01  --preprocessing_flag                    true
% 2.44/1.01  --time_out_prep_mult                    0.1
% 2.44/1.01  --splitting_mode                        input
% 2.44/1.01  --splitting_grd                         true
% 2.44/1.01  --splitting_cvd                         false
% 2.44/1.01  --splitting_cvd_svl                     false
% 2.44/1.01  --splitting_nvd                         32
% 2.44/1.01  --sub_typing                            true
% 2.44/1.01  --prep_gs_sim                           true
% 2.44/1.01  --prep_unflatten                        true
% 2.44/1.01  --prep_res_sim                          true
% 2.44/1.01  --prep_upred                            true
% 2.44/1.01  --prep_sem_filter                       exhaustive
% 2.44/1.01  --prep_sem_filter_out                   false
% 2.44/1.01  --pred_elim                             true
% 2.44/1.01  --res_sim_input                         true
% 2.44/1.01  --eq_ax_congr_red                       true
% 2.44/1.01  --pure_diseq_elim                       true
% 2.44/1.01  --brand_transform                       false
% 2.44/1.01  --non_eq_to_eq                          false
% 2.44/1.01  --prep_def_merge                        true
% 2.44/1.01  --prep_def_merge_prop_impl              false
% 2.44/1.01  --prep_def_merge_mbd                    true
% 2.44/1.01  --prep_def_merge_tr_red                 false
% 2.44/1.01  --prep_def_merge_tr_cl                  false
% 2.44/1.01  --smt_preprocessing                     true
% 2.44/1.01  --smt_ac_axioms                         fast
% 2.44/1.01  --preprocessed_out                      false
% 2.44/1.01  --preprocessed_stats                    false
% 2.44/1.01  
% 2.44/1.01  ------ Abstraction refinement Options
% 2.44/1.01  
% 2.44/1.01  --abstr_ref                             []
% 2.44/1.01  --abstr_ref_prep                        false
% 2.44/1.01  --abstr_ref_until_sat                   false
% 2.44/1.01  --abstr_ref_sig_restrict                funpre
% 2.44/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.01  --abstr_ref_under                       []
% 2.44/1.01  
% 2.44/1.01  ------ SAT Options
% 2.44/1.01  
% 2.44/1.01  --sat_mode                              false
% 2.44/1.01  --sat_fm_restart_options                ""
% 2.44/1.01  --sat_gr_def                            false
% 2.44/1.01  --sat_epr_types                         true
% 2.44/1.01  --sat_non_cyclic_types                  false
% 2.44/1.01  --sat_finite_models                     false
% 2.44/1.01  --sat_fm_lemmas                         false
% 2.44/1.01  --sat_fm_prep                           false
% 2.44/1.01  --sat_fm_uc_incr                        true
% 2.44/1.01  --sat_out_model                         small
% 2.44/1.01  --sat_out_clauses                       false
% 2.44/1.01  
% 2.44/1.01  ------ QBF Options
% 2.44/1.01  
% 2.44/1.01  --qbf_mode                              false
% 2.44/1.01  --qbf_elim_univ                         false
% 2.44/1.01  --qbf_dom_inst                          none
% 2.44/1.01  --qbf_dom_pre_inst                      false
% 2.44/1.01  --qbf_sk_in                             false
% 2.44/1.01  --qbf_pred_elim                         true
% 2.44/1.01  --qbf_split                             512
% 2.44/1.01  
% 2.44/1.01  ------ BMC1 Options
% 2.44/1.01  
% 2.44/1.01  --bmc1_incremental                      false
% 2.44/1.01  --bmc1_axioms                           reachable_all
% 2.44/1.01  --bmc1_min_bound                        0
% 2.44/1.01  --bmc1_max_bound                        -1
% 2.44/1.01  --bmc1_max_bound_default                -1
% 2.44/1.01  --bmc1_symbol_reachability              true
% 2.44/1.01  --bmc1_property_lemmas                  false
% 2.44/1.01  --bmc1_k_induction                      false
% 2.44/1.01  --bmc1_non_equiv_states                 false
% 2.44/1.01  --bmc1_deadlock                         false
% 2.44/1.01  --bmc1_ucm                              false
% 2.44/1.01  --bmc1_add_unsat_core                   none
% 2.44/1.01  --bmc1_unsat_core_children              false
% 2.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.01  --bmc1_out_stat                         full
% 2.44/1.01  --bmc1_ground_init                      false
% 2.44/1.01  --bmc1_pre_inst_next_state              false
% 2.44/1.01  --bmc1_pre_inst_state                   false
% 2.44/1.01  --bmc1_pre_inst_reach_state             false
% 2.44/1.01  --bmc1_out_unsat_core                   false
% 2.44/1.01  --bmc1_aig_witness_out                  false
% 2.44/1.01  --bmc1_verbose                          false
% 2.44/1.01  --bmc1_dump_clauses_tptp                false
% 2.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.01  --bmc1_dump_file                        -
% 2.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.01  --bmc1_ucm_extend_mode                  1
% 2.44/1.01  --bmc1_ucm_init_mode                    2
% 2.44/1.01  --bmc1_ucm_cone_mode                    none
% 2.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.01  --bmc1_ucm_relax_model                  4
% 2.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.01  --bmc1_ucm_layered_model                none
% 2.44/1.01  --bmc1_ucm_max_lemma_size               10
% 2.44/1.01  
% 2.44/1.01  ------ AIG Options
% 2.44/1.01  
% 2.44/1.01  --aig_mode                              false
% 2.44/1.01  
% 2.44/1.01  ------ Instantiation Options
% 2.44/1.01  
% 2.44/1.01  --instantiation_flag                    true
% 2.44/1.01  --inst_sos_flag                         false
% 2.44/1.01  --inst_sos_phase                        true
% 2.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel_side                     none
% 2.44/1.01  --inst_solver_per_active                1400
% 2.44/1.01  --inst_solver_calls_frac                1.
% 2.44/1.01  --inst_passive_queue_type               priority_queues
% 2.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.01  --inst_passive_queues_freq              [25;2]
% 2.44/1.01  --inst_dismatching                      true
% 2.44/1.01  --inst_eager_unprocessed_to_passive     true
% 2.44/1.01  --inst_prop_sim_given                   true
% 2.44/1.01  --inst_prop_sim_new                     false
% 2.44/1.01  --inst_subs_new                         false
% 2.44/1.01  --inst_eq_res_simp                      false
% 2.44/1.01  --inst_subs_given                       false
% 2.44/1.01  --inst_orphan_elimination               true
% 2.44/1.01  --inst_learning_loop_flag               true
% 2.44/1.01  --inst_learning_start                   3000
% 2.44/1.01  --inst_learning_factor                  2
% 2.44/1.01  --inst_start_prop_sim_after_learn       3
% 2.44/1.01  --inst_sel_renew                        solver
% 2.44/1.01  --inst_lit_activity_flag                true
% 2.44/1.01  --inst_restr_to_given                   false
% 2.44/1.01  --inst_activity_threshold               500
% 2.44/1.01  --inst_out_proof                        true
% 2.44/1.01  
% 2.44/1.01  ------ Resolution Options
% 2.44/1.01  
% 2.44/1.01  --resolution_flag                       false
% 2.44/1.01  --res_lit_sel                           adaptive
% 2.44/1.01  --res_lit_sel_side                      none
% 2.44/1.01  --res_ordering                          kbo
% 2.44/1.01  --res_to_prop_solver                    active
% 2.44/1.01  --res_prop_simpl_new                    false
% 2.44/1.01  --res_prop_simpl_given                  true
% 2.44/1.01  --res_passive_queue_type                priority_queues
% 2.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.01  --res_passive_queues_freq               [15;5]
% 2.44/1.01  --res_forward_subs                      full
% 2.44/1.01  --res_backward_subs                     full
% 2.44/1.01  --res_forward_subs_resolution           true
% 2.44/1.01  --res_backward_subs_resolution          true
% 2.44/1.01  --res_orphan_elimination                true
% 2.44/1.01  --res_time_limit                        2.
% 2.44/1.01  --res_out_proof                         true
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Options
% 2.44/1.01  
% 2.44/1.01  --superposition_flag                    true
% 2.44/1.01  --sup_passive_queue_type                priority_queues
% 2.44/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.01  --demod_completeness_check              fast
% 2.44/1.01  --demod_use_ground                      true
% 2.44/1.01  --sup_to_prop_solver                    passive
% 2.44/1.01  --sup_prop_simpl_new                    true
% 2.44/1.01  --sup_prop_simpl_given                  true
% 2.44/1.01  --sup_fun_splitting                     false
% 2.44/1.01  --sup_smt_interval                      50000
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Simplification Setup
% 2.44/1.01  
% 2.44/1.01  --sup_indices_passive                   []
% 2.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_full_bw                           [BwDemod]
% 2.44/1.01  --sup_immed_triv                        [TrivRules]
% 2.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_immed_bw_main                     []
% 2.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  
% 2.44/1.01  ------ Combination Options
% 2.44/1.01  
% 2.44/1.01  --comb_res_mult                         3
% 2.44/1.01  --comb_sup_mult                         2
% 2.44/1.01  --comb_inst_mult                        10
% 2.44/1.01  
% 2.44/1.01  ------ Debug Options
% 2.44/1.01  
% 2.44/1.01  --dbg_backtrace                         false
% 2.44/1.01  --dbg_dump_prop_clauses                 false
% 2.44/1.01  --dbg_dump_prop_clauses_file            -
% 2.44/1.01  --dbg_out_stat                          false
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  ------ Proving...
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  % SZS status Theorem for theBenchmark.p
% 2.44/1.01  
% 2.44/1.01   Resolution empty clause
% 2.44/1.01  
% 2.44/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.01  
% 2.44/1.01  fof(f12,conjecture,(
% 2.44/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f13,negated_conjecture,(
% 2.44/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.44/1.01    inference(negated_conjecture,[],[f12])).
% 2.44/1.01  
% 2.44/1.01  fof(f24,plain,(
% 2.44/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.44/1.01    inference(ennf_transformation,[],[f13])).
% 2.44/1.01  
% 2.44/1.01  fof(f25,plain,(
% 2.44/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.44/1.01    inference(flattening,[],[f24])).
% 2.44/1.01  
% 2.44/1.01  fof(f31,plain,(
% 2.44/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f32,plain,(
% 2.44/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 2.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).
% 2.44/1.01  
% 2.44/1.01  fof(f53,plain,(
% 2.44/1.01    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 2.44/1.01    inference(cnf_transformation,[],[f32])).
% 2.44/1.01  
% 2.44/1.01  fof(f2,axiom,(
% 2.44/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f37,plain,(
% 2.44/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f2])).
% 2.44/1.01  
% 2.44/1.01  fof(f3,axiom,(
% 2.44/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f38,plain,(
% 2.44/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f3])).
% 2.44/1.01  
% 2.44/1.01  fof(f57,plain,(
% 2.44/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.44/1.01    inference(definition_unfolding,[],[f37,f38])).
% 2.44/1.01  
% 2.44/1.01  fof(f66,plain,(
% 2.44/1.01    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2)),
% 2.44/1.01    inference(definition_unfolding,[],[f53,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f11,axiom,(
% 2.44/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f22,plain,(
% 2.44/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(ennf_transformation,[],[f11])).
% 2.44/1.01  
% 2.44/1.01  fof(f23,plain,(
% 2.44/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(flattening,[],[f22])).
% 2.44/1.01  
% 2.44/1.01  fof(f30,plain,(
% 2.44/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(nnf_transformation,[],[f23])).
% 2.44/1.01  
% 2.44/1.01  fof(f46,plain,(
% 2.44/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f30])).
% 2.44/1.01  
% 2.44/1.01  fof(f54,plain,(
% 2.44/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.44/1.01    inference(cnf_transformation,[],[f32])).
% 2.44/1.01  
% 2.44/1.01  fof(f65,plain,(
% 2.44/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 2.44/1.01    inference(definition_unfolding,[],[f54,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f55,plain,(
% 2.44/1.01    k1_xboole_0 != sK2),
% 2.44/1.01    inference(cnf_transformation,[],[f32])).
% 2.44/1.01  
% 2.44/1.01  fof(f9,axiom,(
% 2.44/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f20,plain,(
% 2.44/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(ennf_transformation,[],[f9])).
% 2.44/1.01  
% 2.44/1.01  fof(f44,plain,(
% 2.44/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f20])).
% 2.44/1.01  
% 2.44/1.01  fof(f1,axiom,(
% 2.44/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f26,plain,(
% 2.44/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.44/1.01    inference(nnf_transformation,[],[f1])).
% 2.44/1.01  
% 2.44/1.01  fof(f27,plain,(
% 2.44/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/1.01    inference(rectify,[],[f26])).
% 2.44/1.01  
% 2.44/1.01  fof(f28,plain,(
% 2.44/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f29,plain,(
% 2.44/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.44/1.01  
% 2.44/1.01  fof(f34,plain,(
% 2.44/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.44/1.01    inference(cnf_transformation,[],[f29])).
% 2.44/1.01  
% 2.44/1.01  fof(f60,plain,(
% 2.44/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.44/1.01    inference(definition_unfolding,[],[f34,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f67,plain,(
% 2.44/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.44/1.01    inference(equality_resolution,[],[f60])).
% 2.44/1.01  
% 2.44/1.01  fof(f68,plain,(
% 2.44/1.01    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.44/1.01    inference(equality_resolution,[],[f67])).
% 2.44/1.01  
% 2.44/1.01  fof(f8,axiom,(
% 2.44/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f19,plain,(
% 2.44/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(ennf_transformation,[],[f8])).
% 2.44/1.01  
% 2.44/1.01  fof(f43,plain,(
% 2.44/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f19])).
% 2.44/1.01  
% 2.44/1.01  fof(f7,axiom,(
% 2.44/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f17,plain,(
% 2.44/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.44/1.01    inference(ennf_transformation,[],[f7])).
% 2.44/1.01  
% 2.44/1.01  fof(f18,plain,(
% 2.44/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.44/1.01    inference(flattening,[],[f17])).
% 2.44/1.01  
% 2.44/1.01  fof(f42,plain,(
% 2.44/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f18])).
% 2.44/1.01  
% 2.44/1.01  fof(f63,plain,(
% 2.44/1.01    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.44/1.01    inference(definition_unfolding,[],[f42,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f52,plain,(
% 2.44/1.01    v1_funct_1(sK4)),
% 2.44/1.01    inference(cnf_transformation,[],[f32])).
% 2.44/1.01  
% 2.44/1.01  fof(f4,axiom,(
% 2.44/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f14,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.44/1.01    inference(ennf_transformation,[],[f4])).
% 2.44/1.01  
% 2.44/1.01  fof(f39,plain,(
% 2.44/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f14])).
% 2.44/1.01  
% 2.44/1.01  fof(f62,plain,(
% 2.44/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.44/1.01    inference(definition_unfolding,[],[f39,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f6,axiom,(
% 2.44/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f16,plain,(
% 2.44/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.44/1.01    inference(ennf_transformation,[],[f6])).
% 2.44/1.01  
% 2.44/1.01  fof(f41,plain,(
% 2.44/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f16])).
% 2.44/1.01  
% 2.44/1.01  fof(f56,plain,(
% 2.44/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 2.44/1.01    inference(cnf_transformation,[],[f32])).
% 2.44/1.01  
% 2.44/1.01  fof(f64,plain,(
% 2.44/1.01    ~r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 2.44/1.01    inference(definition_unfolding,[],[f56,f57,f57])).
% 2.44/1.01  
% 2.44/1.01  fof(f10,axiom,(
% 2.44/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f21,plain,(
% 2.44/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.01    inference(ennf_transformation,[],[f10])).
% 2.44/1.01  
% 2.44/1.01  fof(f45,plain,(
% 2.44/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f21])).
% 2.44/1.01  
% 2.44/1.01  fof(f5,axiom,(
% 2.44/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f15,plain,(
% 2.44/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.44/1.01    inference(ennf_transformation,[],[f5])).
% 2.44/1.01  
% 2.44/1.01  fof(f40,plain,(
% 2.44/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f15])).
% 2.44/1.02  
% 2.44/1.02  cnf(c_20,negated_conjecture,
% 2.44/1.02      ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 2.44/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_16,plain,
% 2.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.44/1.02      | k1_xboole_0 = X2 ),
% 2.44/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_19,negated_conjecture,
% 2.44/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 2.44/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_421,plain,
% 2.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.44/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.44/1.02      | sK4 != X0
% 2.44/1.02      | k1_xboole_0 = X2 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_422,plain,
% 2.44/1.02      ( ~ v1_funct_2(sK4,X0,X1)
% 2.44/1.02      | k1_relset_1(X0,X1,sK4) = X0
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.44/1.02      | k1_xboole_0 = X1 ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_421]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_737,plain,
% 2.44/1.02      ( k1_relset_1(X0,X1,sK4) = X0
% 2.44/1.02      | k1_enumset1(sK1,sK1,sK1) != X0
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.44/1.02      | sK4 != sK4
% 2.44/1.02      | sK2 != X1
% 2.44/1.02      | k1_xboole_0 = X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_422]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_738,plain,
% 2.44/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.44/1.02      | k1_xboole_0 = sK2 ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_737]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_18,negated_conjecture,
% 2.44/1.02      ( k1_xboole_0 != sK2 ),
% 2.44/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_739,plain,
% 2.44/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.44/1.02      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.44/1.02      inference(global_propositional_subsumption,[status(thm)],[c_738,c_18]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_740,plain,
% 2.44/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.44/1.02      inference(renaming,[status(thm)],[c_739]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_796,plain,
% 2.44/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.44/1.02      inference(equality_resolution_simp,[status(thm)],[c_740]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_9,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_466,plain,
% 2.44/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.44/1.02      | sK4 != X2 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_467,plain,
% 2.44/1.02      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_466]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1314,plain,
% 2.44/1.02      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 2.44/1.02      inference(equality_resolution,[status(thm)],[c_467]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1378,plain,
% 2.44/1.02      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 2.44/1.02      inference(light_normalisation,[status(thm)],[c_796,c_1314]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2,plain,
% 2.44/1.02      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 2.44/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1202,plain,
% 2.44/1.02      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1440,plain,
% 2.44/1.02      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1378,c_1202]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_8,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_475,plain,
% 2.44/1.02      ( v1_relat_1(X0)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.44/1.02      | sK4 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_476,plain,
% 2.44/1.02      ( v1_relat_1(sK4)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_475]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_7,plain,
% 2.44/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.44/1.02      | ~ v1_funct_1(X1)
% 2.44/1.02      | ~ v1_relat_1(X1)
% 2.44/1.02      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_21,negated_conjecture,
% 2.44/1.02      ( v1_funct_1(sK4) ),
% 2.44/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_263,plain,
% 2.44/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.44/1.02      | ~ v1_relat_1(X1)
% 2.44/1.02      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.44/1.02      | sK4 != X1 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_264,plain,
% 2.44/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.44/1.02      | ~ v1_relat_1(sK4)
% 2.44/1.02      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_263]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_587,plain,
% 2.44/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.44/1.02      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.44/1.02      inference(resolution,[status(thm)],[c_476,c_264]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_938,plain,
% 2.44/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.44/1.02      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | ~ sP3_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.44/1.02                [c_587]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1198,plain,
% 2.44/1.02      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.44/1.02      | sP3_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_939,plain,
% 2.44/1.02      ( sP3_iProver_split | sP0_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[])],
% 2.44/1.02                [c_587]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_981,plain,
% 2.44/1.02      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_982,plain,
% 2.44/1.02      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.44/1.02      | sP3_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_941,plain,( X0 = X0 ),theory(equality) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1315,plain,
% 2.44/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_941]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4,plain,
% 2.44/1.02      ( ~ v1_relat_1(X0)
% 2.44/1.02      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.44/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_622,plain,
% 2.44/1.02      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.44/1.02      | sK4 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_476]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_623,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_622]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_933,plain,
% 2.44/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.44/1.02      | ~ sP0_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.44/1.02                [c_623]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1316,plain,
% 2.44/1.02      ( ~ sP0_iProver_split
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_933]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1321,plain,
% 2.44/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.44/1.02      | sP0_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2526,plain,
% 2.44/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.44/1.02      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_1198,c_981,c_982,c_1315,c_1321]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2527,plain,
% 2.44/1.02      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.44/1.02      inference(renaming,[status(thm)],[c_2526]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2536,plain,
% 2.44/1.02      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1440,c_2527]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_934,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | ~ sP1_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.44/1.02                [c_623]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1192,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.44/1.02      | sP1_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_935,plain,
% 2.44/1.02      ( sP1_iProver_split | sP0_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[])],
% 2.44/1.02                [c_623]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1951,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_1192,c_935,c_934,c_1315,c_1316]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1955,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 2.44/1.02      inference(superposition,[status(thm)],[c_1378,c_1951]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_6,plain,
% 2.44/1.02      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_601,plain,
% 2.44/1.02      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.44/1.02      | sK4 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_476]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_602,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_601]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1317,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.44/1.02      inference(instantiation,[status(thm)],[c_602]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1435,plain,
% 2.44/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_602,c_1315,c_1317]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1960,plain,
% 2.44/1.02      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 2.44/1.02      inference(light_normalisation,[status(thm)],[c_1955,c_1435]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_2538,plain,
% 2.44/1.02      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
% 2.44/1.02      inference(light_normalisation,[status(thm)],[c_2536,c_1960]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_17,negated_conjecture,
% 2.44/1.02      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 2.44/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1200,plain,
% 2.44/1.02      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1383,plain,
% 2.44/1.02      ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.44/1.02      inference(demodulation,[status(thm)],[c_1378,c_1200]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_10,plain,
% 2.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.44/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_457,plain,
% 2.44/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.44/1.02      | sK4 != X2 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_458,plain,
% 2.44/1.02      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_457]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1329,plain,
% 2.44/1.02      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.44/1.02      inference(equality_resolution,[status(thm)],[c_458]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1550,plain,
% 2.44/1.02      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.44/1.02      inference(light_normalisation,[status(thm)],[c_1329,c_1378]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1690,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.44/1.02      inference(demodulation,[status(thm)],[c_1383,c_1550]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_3881,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 2.44/1.02      inference(demodulation,[status(thm)],[c_2538,c_1690]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_5,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.44/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_610,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.44/1.02      | sK4 != X0 ),
% 2.44/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_476]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_611,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
% 2.44/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.44/1.02      inference(unflattening,[status(thm)],[c_610]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_936,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) | ~ sP2_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.44/1.02                [c_611]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1195,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.44/1.02      | sP2_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_937,plain,
% 2.44/1.02      ( sP2_iProver_split | sP0_iProver_split ),
% 2.44/1.02      inference(splitting,
% 2.44/1.02                [splitting(split),new_symbols(definition,[])],
% 2.44/1.02                [c_611]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_976,plain,
% 2.44/1.02      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_977,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.44/1.02      | sP2_iProver_split != iProver_top ),
% 2.44/1.02      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_1876,plain,
% 2.44/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.44/1.02      inference(global_propositional_subsumption,
% 2.44/1.02                [status(thm)],
% 2.44/1.02                [c_1195,c_976,c_977,c_1315,c_1321]) ).
% 2.44/1.02  
% 2.44/1.02  cnf(c_4164,plain,
% 2.44/1.02      ( $false ),
% 2.44/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3881,c_1876]) ).
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.02  
% 2.44/1.02  ------                               Statistics
% 2.44/1.02  
% 2.44/1.02  ------ General
% 2.44/1.02  
% 2.44/1.02  abstr_ref_over_cycles:                  0
% 2.44/1.02  abstr_ref_under_cycles:                 0
% 2.44/1.02  gc_basic_clause_elim:                   0
% 2.44/1.02  forced_gc_time:                         0
% 2.44/1.02  parsing_time:                           0.009
% 2.44/1.02  unif_index_cands_time:                  0.
% 2.44/1.02  unif_index_add_time:                    0.
% 2.44/1.02  orderings_time:                         0.
% 2.44/1.02  out_proof_time:                         0.008
% 2.44/1.02  total_time:                             0.156
% 2.44/1.02  num_of_symbols:                         57
% 2.44/1.02  num_of_terms:                           3929
% 2.44/1.02  
% 2.44/1.02  ------ Preprocessing
% 2.44/1.02  
% 2.44/1.02  num_of_splits:                          6
% 2.44/1.02  num_of_split_atoms:                     4
% 2.44/1.02  num_of_reused_defs:                     2
% 2.44/1.02  num_eq_ax_congr_red:                    16
% 2.44/1.02  num_of_sem_filtered_clauses:            1
% 2.44/1.02  num_of_subtypes:                        0
% 2.44/1.02  monotx_restored_types:                  0
% 2.44/1.02  sat_num_of_epr_types:                   0
% 2.44/1.02  sat_num_of_non_cyclic_types:            0
% 2.44/1.02  sat_guarded_non_collapsed_types:        0
% 2.44/1.02  num_pure_diseq_elim:                    0
% 2.44/1.02  simp_replaced_by:                       0
% 2.44/1.02  res_preprocessed:                       104
% 2.44/1.02  prep_upred:                             0
% 2.44/1.02  prep_unflattend:                        51
% 2.44/1.02  smt_new_axioms:                         0
% 2.44/1.02  pred_elim_cands:                        2
% 2.44/1.02  pred_elim:                              4
% 2.44/1.02  pred_elim_cl:                           7
% 2.44/1.02  pred_elim_cycles:                       12
% 2.44/1.02  merged_defs:                            0
% 2.44/1.02  merged_defs_ncl:                        0
% 2.44/1.02  bin_hyper_res:                          0
% 2.44/1.02  prep_cycles:                            4
% 2.44/1.02  pred_elim_time:                         0.013
% 2.44/1.02  splitting_time:                         0.
% 2.44/1.02  sem_filter_time:                        0.
% 2.44/1.02  monotx_time:                            0.
% 2.44/1.02  subtype_inf_time:                       0.
% 2.44/1.02  
% 2.44/1.02  ------ Problem properties
% 2.44/1.02  
% 2.44/1.02  clauses:                                21
% 2.44/1.02  conjectures:                            2
% 2.44/1.02  epr:                                    4
% 2.44/1.02  horn:                                   16
% 2.44/1.02  ground:                                 8
% 2.44/1.02  unary:                                  4
% 2.44/1.02  binary:                                 12
% 2.44/1.02  lits:                                   44
% 2.44/1.02  lits_eq:                                25
% 2.44/1.02  fd_pure:                                0
% 2.44/1.02  fd_pseudo:                              0
% 2.44/1.02  fd_cond:                                0
% 2.44/1.02  fd_pseudo_cond:                         2
% 2.44/1.02  ac_symbols:                             0
% 2.44/1.02  
% 2.44/1.02  ------ Propositional Solver
% 2.44/1.02  
% 2.44/1.02  prop_solver_calls:                      27
% 2.44/1.02  prop_fast_solver_calls:                 712
% 2.44/1.02  smt_solver_calls:                       0
% 2.44/1.02  smt_fast_solver_calls:                  0
% 2.44/1.02  prop_num_of_clauses:                    1431
% 2.44/1.02  prop_preprocess_simplified:             4240
% 2.44/1.02  prop_fo_subsumed:                       12
% 2.44/1.02  prop_solver_time:                       0.
% 2.44/1.02  smt_solver_time:                        0.
% 2.44/1.02  smt_fast_solver_time:                   0.
% 2.44/1.02  prop_fast_solver_time:                  0.
% 2.44/1.02  prop_unsat_core_time:                   0.
% 2.44/1.02  
% 2.44/1.02  ------ QBF
% 2.44/1.02  
% 2.44/1.02  qbf_q_res:                              0
% 2.44/1.02  qbf_num_tautologies:                    0
% 2.44/1.02  qbf_prep_cycles:                        0
% 2.44/1.02  
% 2.44/1.02  ------ BMC1
% 2.44/1.02  
% 2.44/1.02  bmc1_current_bound:                     -1
% 2.44/1.02  bmc1_last_solved_bound:                 -1
% 2.44/1.02  bmc1_unsat_core_size:                   -1
% 2.44/1.02  bmc1_unsat_core_parents_size:           -1
% 2.44/1.02  bmc1_merge_next_fun:                    0
% 2.44/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.02  
% 2.44/1.02  ------ Instantiation
% 2.44/1.02  
% 2.44/1.02  inst_num_of_clauses:                    435
% 2.44/1.02  inst_num_in_passive:                    110
% 2.44/1.02  inst_num_in_active:                     174
% 2.44/1.02  inst_num_in_unprocessed:                151
% 2.44/1.02  inst_num_of_loops:                      210
% 2.44/1.02  inst_num_of_learning_restarts:          0
% 2.44/1.02  inst_num_moves_active_passive:          33
% 2.44/1.02  inst_lit_activity:                      0
% 2.44/1.02  inst_lit_activity_moves:                0
% 2.44/1.02  inst_num_tautologies:                   0
% 2.44/1.02  inst_num_prop_implied:                  0
% 2.44/1.02  inst_num_existing_simplified:           0
% 2.44/1.02  inst_num_eq_res_simplified:             0
% 2.44/1.02  inst_num_child_elim:                    0
% 2.44/1.02  inst_num_of_dismatching_blockings:      137
% 2.44/1.02  inst_num_of_non_proper_insts:           374
% 2.44/1.02  inst_num_of_duplicates:                 0
% 2.44/1.02  inst_inst_num_from_inst_to_res:         0
% 2.44/1.02  inst_dismatching_checking_time:         0.
% 2.44/1.02  
% 2.44/1.02  ------ Resolution
% 2.44/1.02  
% 2.44/1.02  res_num_of_clauses:                     0
% 2.44/1.02  res_num_in_passive:                     0
% 2.44/1.02  res_num_in_active:                      0
% 2.44/1.02  res_num_of_loops:                       108
% 2.44/1.02  res_forward_subset_subsumed:            84
% 2.44/1.02  res_backward_subset_subsumed:           0
% 2.44/1.02  res_forward_subsumed:                   0
% 2.44/1.02  res_backward_subsumed:                  0
% 2.44/1.02  res_forward_subsumption_resolution:     0
% 2.44/1.02  res_backward_subsumption_resolution:    0
% 2.44/1.02  res_clause_to_clause_subsumption:       495
% 2.44/1.02  res_orphan_elimination:                 0
% 2.44/1.02  res_tautology_del:                      26
% 2.44/1.02  res_num_eq_res_simplified:              1
% 2.44/1.02  res_num_sel_changes:                    0
% 2.44/1.02  res_moves_from_active_to_pass:          0
% 2.44/1.02  
% 2.44/1.02  ------ Superposition
% 2.44/1.02  
% 2.44/1.02  sup_time_total:                         0.
% 2.44/1.02  sup_time_generating:                    0.
% 2.44/1.02  sup_time_sim_full:                      0.
% 2.44/1.02  sup_time_sim_immed:                     0.
% 2.44/1.02  
% 2.44/1.02  sup_num_of_clauses:                     89
% 2.44/1.02  sup_num_in_active:                      34
% 2.44/1.02  sup_num_in_passive:                     55
% 2.44/1.02  sup_num_of_loops:                       40
% 2.44/1.02  sup_fw_superposition:                   57
% 2.44/1.02  sup_bw_superposition:                   61
% 2.44/1.02  sup_immediate_simplified:               29
% 2.44/1.02  sup_given_eliminated:                   0
% 2.44/1.02  comparisons_done:                       0
% 2.44/1.02  comparisons_avoided:                    14
% 2.44/1.02  
% 2.44/1.02  ------ Simplifications
% 2.44/1.02  
% 2.44/1.02  
% 2.44/1.02  sim_fw_subset_subsumed:                 7
% 2.44/1.02  sim_bw_subset_subsumed:                 0
% 2.44/1.02  sim_fw_subsumed:                        5
% 2.44/1.02  sim_bw_subsumed:                        0
% 2.44/1.02  sim_fw_subsumption_res:                 2
% 2.44/1.02  sim_bw_subsumption_res:                 0
% 2.44/1.02  sim_tautology_del:                      3
% 2.44/1.02  sim_eq_tautology_del:                   2
% 2.44/1.02  sim_eq_res_simp:                        0
% 2.44/1.02  sim_fw_demodulated:                     3
% 2.44/1.02  sim_bw_demodulated:                     6
% 2.44/1.02  sim_light_normalised:                   17
% 2.44/1.02  sim_joinable_taut:                      0
% 2.44/1.02  sim_joinable_simp:                      0
% 2.44/1.02  sim_ac_normalised:                      0
% 2.44/1.02  sim_smt_subsumption:                    0
% 2.44/1.02  
%------------------------------------------------------------------------------
