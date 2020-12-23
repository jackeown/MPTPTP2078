%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:51 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 718 expanded)
%              Number of clauses        :   66 ( 190 expanded)
%              Number of leaves         :   20 ( 164 expanded)
%              Depth                    :   32
%              Number of atoms          :  405 (1810 expanded)
%              Number of equality atoms :  209 ( 790 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f43])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f58,f77,f77])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f94,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f95,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f94])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f69,f76,f76])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f75,f77,f77])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33332,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_322,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_323,plain,
    ( v4_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_367,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_323])).

cnf(c_368,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_33323,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_33499,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_33323])).

cnf(c_33479,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_33480,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33479])).

cnf(c_528,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_33511,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33334,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_298,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_299,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_33325,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_33477,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_33325])).

cnf(c_33514,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_33334,c_33477])).

cnf(c_33534,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33499,c_33480,c_33511,c_33514])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33335,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_33670,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33534,c_33335])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_33339,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_33747,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33670,c_33339])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_33324,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_33894,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_33747,c_33324])).

cnf(c_33902,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33894,c_33514])).

cnf(c_33903,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33902])).

cnf(c_33911,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33747,c_33903])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_313,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_314,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_33450,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_314])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_33329,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33468,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33450,c_33329])).

cnf(c_33918,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK3),k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33911,c_33468])).

cnf(c_33988,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK3),k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33670,c_33918])).

cnf(c_33993,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_33332,c_33988])).

cnf(c_33996,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33993,c_33514])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33330,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34027,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_33996,c_33330])).

cnf(c_34096,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34027,c_33514])).

cnf(c_17,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33333,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_34101,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_34096,c_33333])).

cnf(c_34218,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34101,c_33514])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33341,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_33343,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_33616,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_33341,c_33343])).

cnf(c_34226,plain,
    ( k9_relat_1(sK4,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34218,c_33616])).

cnf(c_34289,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34226,c_33468])).

cnf(c_34383,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_34289,c_33341])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:28:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.96/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.96/1.48  
% 7.96/1.48  ------  iProver source info
% 7.96/1.48  
% 7.96/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.96/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.96/1.48  git: non_committed_changes: false
% 7.96/1.48  git: last_make_outside_of_git: false
% 7.96/1.48  
% 7.96/1.48  ------ 
% 7.96/1.48  ------ Parsing...
% 7.96/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  ------ Proving...
% 7.96/1.48  ------ Problem Properties 
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  clauses                                 23
% 7.96/1.48  conjectures                             2
% 7.96/1.48  EPR                                     4
% 7.96/1.48  Horn                                    20
% 7.96/1.48  unary                                   9
% 7.96/1.48  binary                                  3
% 7.96/1.48  lits                                    50
% 7.96/1.48  lits eq                                 22
% 7.96/1.48  fd_pure                                 0
% 7.96/1.48  fd_pseudo                               0
% 7.96/1.48  fd_cond                                 0
% 7.96/1.48  fd_pseudo_cond                          5
% 7.96/1.48  AC symbols                              0
% 7.96/1.48  
% 7.96/1.48  ------ Input Options Time Limit: Unbounded
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.96/1.48  Current options:
% 7.96/1.48  ------ 
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  % SZS status Theorem for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48   Resolution empty clause
% 7.96/1.48  
% 7.96/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  fof(f12,axiom,(
% 7.96/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f24,plain,(
% 7.96/1.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.96/1.48    inference(ennf_transformation,[],[f12])).
% 7.96/1.48  
% 7.96/1.48  fof(f66,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f24])).
% 7.96/1.48  
% 7.96/1.48  fof(f9,axiom,(
% 7.96/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f22,plain,(
% 7.96/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.96/1.48    inference(ennf_transformation,[],[f9])).
% 7.96/1.48  
% 7.96/1.48  fof(f41,plain,(
% 7.96/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.96/1.48    inference(nnf_transformation,[],[f22])).
% 7.96/1.48  
% 7.96/1.48  fof(f62,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f41])).
% 7.96/1.48  
% 7.96/1.48  fof(f15,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f20,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.96/1.48    inference(pure_predicate_removal,[],[f15])).
% 7.96/1.48  
% 7.96/1.48  fof(f28,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.96/1.48    inference(ennf_transformation,[],[f20])).
% 7.96/1.48  
% 7.96/1.48  fof(f70,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f28])).
% 7.96/1.48  
% 7.96/1.48  fof(f17,conjecture,(
% 7.96/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f18,negated_conjecture,(
% 7.96/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.96/1.48    inference(negated_conjecture,[],[f17])).
% 7.96/1.48  
% 7.96/1.48  fof(f19,plain,(
% 7.96/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.96/1.48    inference(pure_predicate_removal,[],[f18])).
% 7.96/1.48  
% 7.96/1.48  fof(f30,plain,(
% 7.96/1.48    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.96/1.48    inference(ennf_transformation,[],[f19])).
% 7.96/1.48  
% 7.96/1.48  fof(f31,plain,(
% 7.96/1.48    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.96/1.48    inference(flattening,[],[f30])).
% 7.96/1.48  
% 7.96/1.48  fof(f43,plain,(
% 7.96/1.48    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4))),
% 7.96/1.48    introduced(choice_axiom,[])).
% 7.96/1.48  
% 7.96/1.48  fof(f44,plain,(
% 7.96/1.48    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_1(sK4)),
% 7.96/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f43])).
% 7.96/1.48  
% 7.96/1.48  fof(f73,plain,(
% 7.96/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 7.96/1.48    inference(cnf_transformation,[],[f44])).
% 7.96/1.48  
% 7.96/1.48  fof(f4,axiom,(
% 7.96/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f55,plain,(
% 7.96/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f4])).
% 7.96/1.48  
% 7.96/1.48  fof(f5,axiom,(
% 7.96/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f56,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f5])).
% 7.96/1.48  
% 7.96/1.48  fof(f6,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f57,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f6])).
% 7.96/1.48  
% 7.96/1.48  fof(f76,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.96/1.48    inference(definition_unfolding,[],[f56,f57])).
% 7.96/1.48  
% 7.96/1.48  fof(f77,plain,(
% 7.96/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.96/1.48    inference(definition_unfolding,[],[f55,f76])).
% 7.96/1.48  
% 7.96/1.48  fof(f89,plain,(
% 7.96/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 7.96/1.48    inference(definition_unfolding,[],[f73,f77])).
% 7.96/1.48  
% 7.96/1.48  fof(f10,axiom,(
% 7.96/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f64,plain,(
% 7.96/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f10])).
% 7.96/1.48  
% 7.96/1.48  fof(f8,axiom,(
% 7.96/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f21,plain,(
% 7.96/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.96/1.48    inference(ennf_transformation,[],[f8])).
% 7.96/1.48  
% 7.96/1.48  fof(f61,plain,(
% 7.96/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f21])).
% 7.96/1.48  
% 7.96/1.48  fof(f7,axiom,(
% 7.96/1.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f39,plain,(
% 7.96/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.96/1.48    inference(nnf_transformation,[],[f7])).
% 7.96/1.48  
% 7.96/1.48  fof(f40,plain,(
% 7.96/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.96/1.48    inference(flattening,[],[f39])).
% 7.96/1.48  
% 7.96/1.48  fof(f58,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f40])).
% 7.96/1.48  
% 7.96/1.48  fof(f86,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.96/1.48    inference(definition_unfolding,[],[f58,f77,f77])).
% 7.96/1.48  
% 7.96/1.48  fof(f3,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f34,plain,(
% 7.96/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.96/1.48    inference(nnf_transformation,[],[f3])).
% 7.96/1.48  
% 7.96/1.48  fof(f35,plain,(
% 7.96/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.96/1.48    inference(flattening,[],[f34])).
% 7.96/1.48  
% 7.96/1.48  fof(f36,plain,(
% 7.96/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.96/1.48    inference(rectify,[],[f35])).
% 7.96/1.48  
% 7.96/1.48  fof(f37,plain,(
% 7.96/1.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.96/1.48    introduced(choice_axiom,[])).
% 7.96/1.48  
% 7.96/1.48  fof(f38,plain,(
% 7.96/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.96/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 7.96/1.48  
% 7.96/1.48  fof(f50,plain,(
% 7.96/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.96/1.48    inference(cnf_transformation,[],[f38])).
% 7.96/1.48  
% 7.96/1.48  fof(f82,plain,(
% 7.96/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.96/1.48    inference(definition_unfolding,[],[f50,f76])).
% 7.96/1.48  
% 7.96/1.48  fof(f94,plain,(
% 7.96/1.48    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.96/1.48    inference(equality_resolution,[],[f82])).
% 7.96/1.48  
% 7.96/1.48  fof(f95,plain,(
% 7.96/1.48    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.96/1.48    inference(equality_resolution,[],[f94])).
% 7.96/1.48  
% 7.96/1.48  fof(f14,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f26,plain,(
% 7.96/1.48    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.96/1.48    inference(ennf_transformation,[],[f14])).
% 7.96/1.48  
% 7.96/1.48  fof(f27,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.96/1.48    inference(flattening,[],[f26])).
% 7.96/1.48  
% 7.96/1.48  fof(f69,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f27])).
% 7.96/1.48  
% 7.96/1.48  fof(f87,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.96/1.48    inference(definition_unfolding,[],[f69,f76,f76])).
% 7.96/1.48  
% 7.96/1.48  fof(f72,plain,(
% 7.96/1.48    v1_funct_1(sK4)),
% 7.96/1.48    inference(cnf_transformation,[],[f44])).
% 7.96/1.48  
% 7.96/1.48  fof(f16,axiom,(
% 7.96/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f29,plain,(
% 7.96/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.96/1.48    inference(ennf_transformation,[],[f16])).
% 7.96/1.48  
% 7.96/1.48  fof(f71,plain,(
% 7.96/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f29])).
% 7.96/1.48  
% 7.96/1.48  fof(f75,plain,(
% 7.96/1.48    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 7.96/1.48    inference(cnf_transformation,[],[f44])).
% 7.96/1.48  
% 7.96/1.48  fof(f88,plain,(
% 7.96/1.48    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 7.96/1.48    inference(definition_unfolding,[],[f75,f77,f77])).
% 7.96/1.48  
% 7.96/1.48  fof(f13,axiom,(
% 7.96/1.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f25,plain,(
% 7.96/1.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.96/1.48    inference(ennf_transformation,[],[f13])).
% 7.96/1.48  
% 7.96/1.48  fof(f42,plain,(
% 7.96/1.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.96/1.48    inference(nnf_transformation,[],[f25])).
% 7.96/1.48  
% 7.96/1.48  fof(f67,plain,(
% 7.96/1.48    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f42])).
% 7.96/1.48  
% 7.96/1.48  fof(f11,axiom,(
% 7.96/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f23,plain,(
% 7.96/1.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.96/1.48    inference(ennf_transformation,[],[f11])).
% 7.96/1.48  
% 7.96/1.48  fof(f65,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f23])).
% 7.96/1.48  
% 7.96/1.48  fof(f2,axiom,(
% 7.96/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f48,plain,(
% 7.96/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f2])).
% 7.96/1.48  
% 7.96/1.48  fof(f1,axiom,(
% 7.96/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f32,plain,(
% 7.96/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.96/1.48    inference(nnf_transformation,[],[f1])).
% 7.96/1.48  
% 7.96/1.48  fof(f33,plain,(
% 7.96/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.96/1.48    inference(flattening,[],[f32])).
% 7.96/1.48  
% 7.96/1.48  fof(f47,plain,(
% 7.96/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f33])).
% 7.96/1.48  
% 7.96/1.48  cnf(c_18,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 7.96/1.48      | ~ v1_relat_1(X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33332,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
% 7.96/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_15,plain,
% 7.96/1.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_22,plain,
% 7.96/1.48      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.96/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_26,negated_conjecture,
% 7.96/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 7.96/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_322,plain,
% 7.96/1.48      ( v4_relat_1(X0,X1)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.96/1.48      | sK4 != X0 ),
% 7.96/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_323,plain,
% 7.96/1.48      ( v4_relat_1(sK4,X0)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.96/1.48      inference(unflattening,[status(thm)],[c_322]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_367,plain,
% 7.96/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.96/1.48      | ~ v1_relat_1(X0)
% 7.96/1.48      | X2 != X1
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 7.96/1.48      | sK4 != X0 ),
% 7.96/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_323]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_368,plain,
% 7.96/1.48      ( r1_tarski(k1_relat_1(sK4),X0)
% 7.96/1.48      | ~ v1_relat_1(sK4)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.96/1.48      inference(unflattening,[status(thm)],[c_367]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33323,plain,
% 7.96/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.96/1.48      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33499,plain,
% 7.96/1.48      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(equality_resolution,[status(thm)],[c_33323]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33479,plain,
% 7.96/1.48      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1))
% 7.96/1.48      | ~ v1_relat_1(sK4)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_368]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33480,plain,
% 7.96/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 7.96/1.48      | r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_33479]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_528,plain,( X0 = X0 ),theory(equality) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33511,plain,
% 7.96/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_528]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_16,plain,
% 7.96/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.96/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33334,plain,
% 7.96/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_13,plain,
% 7.96/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_298,plain,
% 7.96/1.48      ( ~ v1_relat_1(X0)
% 7.96/1.48      | v1_relat_1(X1)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 7.96/1.48      | sK4 != X1 ),
% 7.96/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_299,plain,
% 7.96/1.48      ( ~ v1_relat_1(X0)
% 7.96/1.48      | v1_relat_1(sK4)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 7.96/1.48      inference(unflattening,[status(thm)],[c_298]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33325,plain,
% 7.96/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 7.96/1.48      | v1_relat_1(X0) != iProver_top
% 7.96/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33477,plain,
% 7.96/1.48      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
% 7.96/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.96/1.48      inference(equality_resolution,[status(thm)],[c_33325]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33514,plain,
% 7.96/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33334,c_33477]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33534,plain,
% 7.96/1.48      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.96/1.48      inference(global_propositional_subsumption,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_33499,c_33480,c_33511,c_33514]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_12,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 7.96/1.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.96/1.48      | k1_xboole_0 = X0 ),
% 7.96/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33335,plain,
% 7.96/1.48      ( k2_enumset1(X0,X0,X0,X0) = X1
% 7.96/1.48      | k1_xboole_0 = X1
% 7.96/1.48      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33670,plain,
% 7.96/1.48      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4)
% 7.96/1.48      | k1_relat_1(sK4) = k1_xboole_0 ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33534,c_33335]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_8,plain,
% 7.96/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.96/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33339,plain,
% 7.96/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33747,plain,
% 7.96/1.48      ( k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33670,c_33339]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_21,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.96/1.48      | ~ r2_hidden(X2,k1_relat_1(X1))
% 7.96/1.48      | ~ v1_funct_1(X1)
% 7.96/1.48      | ~ v1_relat_1(X1)
% 7.96/1.48      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 7.96/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_27,negated_conjecture,
% 7.96/1.48      ( v1_funct_1(sK4) ),
% 7.96/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_343,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.96/1.48      | ~ r2_hidden(X2,k1_relat_1(X1))
% 7.96/1.48      | ~ v1_relat_1(X1)
% 7.96/1.48      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
% 7.96/1.48      | sK4 != X1 ),
% 7.96/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_344,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 7.96/1.48      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 7.96/1.48      | ~ v1_relat_1(sK4)
% 7.96/1.48      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1)) ),
% 7.96/1.48      inference(unflattening,[status(thm)],[c_343]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33324,plain,
% 7.96/1.48      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X1))
% 7.96/1.48      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 7.96/1.48      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33894,plain,
% 7.96/1.48      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
% 7.96/1.48      | k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33747,c_33324]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33902,plain,
% 7.96/1.48      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 7.96/1.48      | k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0)) ),
% 7.96/1.48      inference(global_propositional_subsumption,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_33894,c_33514]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33903,plain,
% 7.96/1.48      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,X0))
% 7.96/1.48      | k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 7.96/1.48      inference(renaming,[status(thm)],[c_33902]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33911,plain,
% 7.96/1.48      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.96/1.48      | k1_relat_1(sK4) = k1_xboole_0 ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33747,c_33903]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_23,plain,
% 7.96/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.96/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.96/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_313,plain,
% 7.96/1.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.96/1.48      | sK4 != X2 ),
% 7.96/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_314,plain,
% 7.96/1.48      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 7.96/1.48      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.96/1.48      inference(unflattening,[status(thm)],[c_313]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33450,plain,
% 7.96/1.48      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 7.96/1.48      inference(equality_resolution,[status(thm)],[c_314]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_24,negated_conjecture,
% 7.96/1.48      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 7.96/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33329,plain,
% 7.96/1.48      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33468,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 7.96/1.48      inference(demodulation,[status(thm)],[c_33450,c_33329]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33918,plain,
% 7.96/1.48      ( k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | r1_tarski(k9_relat_1(sK4,sK3),k9_relat_1(sK4,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33911,c_33468]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33988,plain,
% 7.96/1.48      ( k1_relat_1(sK4) = k1_xboole_0
% 7.96/1.48      | r1_tarski(k9_relat_1(sK4,sK3),k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33670,c_33918]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33993,plain,
% 7.96/1.48      ( k1_relat_1(sK4) = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33332,c_33988]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33996,plain,
% 7.96/1.48      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.96/1.48      inference(global_propositional_subsumption,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_33993,c_33514]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_20,plain,
% 7.96/1.48      ( ~ v1_relat_1(X0)
% 7.96/1.48      | k2_relat_1(X0) = k1_xboole_0
% 7.96/1.48      | k1_relat_1(X0) != k1_xboole_0 ),
% 7.96/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33330,plain,
% 7.96/1.48      ( k2_relat_1(X0) = k1_xboole_0
% 7.96/1.48      | k1_relat_1(X0) != k1_xboole_0
% 7.96/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34027,plain,
% 7.96/1.48      ( k2_relat_1(sK4) = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33996,c_33330]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34096,plain,
% 7.96/1.48      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 7.96/1.48      inference(global_propositional_subsumption,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_34027,c_33514]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_17,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33333,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 7.96/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34101,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) = iProver_top
% 7.96/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_34096,c_33333]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34218,plain,
% 7.96/1.48      ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) = iProver_top ),
% 7.96/1.48      inference(global_propositional_subsumption,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_34101,c_33514]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_3,plain,
% 7.96/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33341,plain,
% 7.96/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_0,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.96/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33343,plain,
% 7.96/1.48      ( X0 = X1
% 7.96/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.96/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.96/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33616,plain,
% 7.96/1.48      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_33341,c_33343]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34226,plain,
% 7.96/1.48      ( k9_relat_1(sK4,X0) = k1_xboole_0 ),
% 7.96/1.48      inference(superposition,[status(thm)],[c_34218,c_33616]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34289,plain,
% 7.96/1.48      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 7.96/1.48      inference(demodulation,[status(thm)],[c_34226,c_33468]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34383,plain,
% 7.96/1.48      ( $false ),
% 7.96/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_34289,c_33341]) ).
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  ------                               Statistics
% 7.96/1.48  
% 7.96/1.48  ------ Selected
% 7.96/1.48  
% 7.96/1.48  total_time:                             0.798
% 7.96/1.48  
%------------------------------------------------------------------------------
