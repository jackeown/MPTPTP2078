%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:07 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 182 expanded)
%              Number of clauses        :   45 (  48 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   19
%              Number of atoms          :  385 ( 629 expanded)
%              Number of equality atoms :  180 ( 250 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK5,sK4) != sK3
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39])).

fof(f70,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f85,plain,(
    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f89,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f90,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f89])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f88,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f71,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2251,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_enumset1(sK3,sK3,sK3) != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
    | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_430,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_26])).

cnf(c_2250,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2252,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2929,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2250,c_2252])).

cnf(c_3027,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(superposition,[status(thm)],[c_430,c_2929])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_912,plain,
    ( X0 != X1
    | k1_enumset1(X2,X2,X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_313])).

cnf(c_913,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_3031,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3027,c_913])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_335,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_336,plain,
    ( ~ v5_relat_1(sK5,X0)
    | m1_subset_1(k1_funct_1(sK5,X1),X0)
    | ~ r2_hidden(X1,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(sK5,X3),X4)
    | ~ r2_hidden(X3,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | X4 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_336])).

cnf(c_359,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_371,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_359,c_15])).

cnf(c_2248,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_2446,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_2248])).

cnf(c_3033,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3031,c_2446])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2253,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3382,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_2253])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2254,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4052,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3382,c_2254])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2261,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4056,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_2261])).

cnf(c_4065,plain,
    ( k1_funct_1(sK5,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_2251,c_4056])).

cnf(c_24,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4065,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n018.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:13:12 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 2.74/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/0.96  
% 2.74/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.96  
% 2.74/0.96  ------  iProver source info
% 2.74/0.96  
% 2.74/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.96  git: non_committed_changes: false
% 2.74/0.96  git: last_make_outside_of_git: false
% 2.74/0.96  
% 2.74/0.96  ------ 
% 2.74/0.96  
% 2.74/0.96  ------ Input Options
% 2.74/0.96  
% 2.74/0.96  --out_options                           all
% 2.74/0.96  --tptp_safe_out                         true
% 2.74/0.96  --problem_path                          ""
% 2.74/0.96  --include_path                          ""
% 2.74/0.96  --clausifier                            res/vclausify_rel
% 2.74/0.96  --clausifier_options                    --mode clausify
% 2.74/0.96  --stdin                                 false
% 2.74/0.96  --stats_out                             all
% 2.74/0.96  
% 2.74/0.96  ------ General Options
% 2.74/0.96  
% 2.74/0.96  --fof                                   false
% 2.74/0.96  --time_out_real                         305.
% 2.74/0.96  --time_out_virtual                      -1.
% 2.74/0.96  --symbol_type_check                     false
% 2.74/0.96  --clausify_out                          false
% 2.74/0.96  --sig_cnt_out                           false
% 2.74/0.96  --trig_cnt_out                          false
% 2.74/0.96  --trig_cnt_out_tolerance                1.
% 2.74/0.96  --trig_cnt_out_sk_spl                   false
% 2.74/0.96  --abstr_cl_out                          false
% 2.74/0.96  
% 2.74/0.96  ------ Global Options
% 2.74/0.96  
% 2.74/0.96  --schedule                              default
% 2.74/0.96  --add_important_lit                     false
% 2.74/0.96  --prop_solver_per_cl                    1000
% 2.74/0.96  --min_unsat_core                        false
% 2.74/0.96  --soft_assumptions                      false
% 2.74/0.96  --soft_lemma_size                       3
% 2.74/0.96  --prop_impl_unit_size                   0
% 2.74/0.96  --prop_impl_unit                        []
% 2.74/0.96  --share_sel_clauses                     true
% 2.74/0.96  --reset_solvers                         false
% 2.74/0.96  --bc_imp_inh                            [conj_cone]
% 2.74/0.96  --conj_cone_tolerance                   3.
% 2.74/0.96  --extra_neg_conj                        none
% 2.74/0.96  --large_theory_mode                     true
% 2.74/0.96  --prolific_symb_bound                   200
% 2.74/0.96  --lt_threshold                          2000
% 2.74/0.96  --clause_weak_htbl                      true
% 2.74/0.96  --gc_record_bc_elim                     false
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing Options
% 2.74/0.96  
% 2.74/0.96  --preprocessing_flag                    true
% 2.74/0.96  --time_out_prep_mult                    0.1
% 2.74/0.96  --splitting_mode                        input
% 2.74/0.96  --splitting_grd                         true
% 2.74/0.96  --splitting_cvd                         false
% 2.74/0.96  --splitting_cvd_svl                     false
% 2.74/0.96  --splitting_nvd                         32
% 2.74/0.96  --sub_typing                            true
% 2.74/0.96  --prep_gs_sim                           true
% 2.74/0.96  --prep_unflatten                        true
% 2.74/0.96  --prep_res_sim                          true
% 2.74/0.96  --prep_upred                            true
% 2.74/0.96  --prep_sem_filter                       exhaustive
% 2.74/0.96  --prep_sem_filter_out                   false
% 2.74/0.96  --pred_elim                             true
% 2.74/0.96  --res_sim_input                         true
% 2.74/0.96  --eq_ax_congr_red                       true
% 2.74/0.96  --pure_diseq_elim                       true
% 2.74/0.96  --brand_transform                       false
% 2.74/0.96  --non_eq_to_eq                          false
% 2.74/0.96  --prep_def_merge                        true
% 2.74/0.96  --prep_def_merge_prop_impl              false
% 2.74/0.96  --prep_def_merge_mbd                    true
% 2.74/0.96  --prep_def_merge_tr_red                 false
% 2.74/0.96  --prep_def_merge_tr_cl                  false
% 2.74/0.96  --smt_preprocessing                     true
% 2.74/0.96  --smt_ac_axioms                         fast
% 2.74/0.96  --preprocessed_out                      false
% 2.74/0.96  --preprocessed_stats                    false
% 2.74/0.96  
% 2.74/0.96  ------ Abstraction refinement Options
% 2.74/0.96  
% 2.74/0.96  --abstr_ref                             []
% 2.74/0.96  --abstr_ref_prep                        false
% 2.74/0.96  --abstr_ref_until_sat                   false
% 2.74/0.96  --abstr_ref_sig_restrict                funpre
% 2.74/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.96  --abstr_ref_under                       []
% 2.74/0.96  
% 2.74/0.96  ------ SAT Options
% 2.74/0.96  
% 2.74/0.96  --sat_mode                              false
% 2.74/0.96  --sat_fm_restart_options                ""
% 2.74/0.96  --sat_gr_def                            false
% 2.74/0.96  --sat_epr_types                         true
% 2.74/0.96  --sat_non_cyclic_types                  false
% 2.74/0.96  --sat_finite_models                     false
% 2.74/0.96  --sat_fm_lemmas                         false
% 2.74/0.96  --sat_fm_prep                           false
% 2.74/0.96  --sat_fm_uc_incr                        true
% 2.74/0.96  --sat_out_model                         small
% 2.74/0.96  --sat_out_clauses                       false
% 2.74/0.96  
% 2.74/0.96  ------ QBF Options
% 2.74/0.96  
% 2.74/0.96  --qbf_mode                              false
% 2.74/0.96  --qbf_elim_univ                         false
% 2.74/0.96  --qbf_dom_inst                          none
% 2.74/0.96  --qbf_dom_pre_inst                      false
% 2.74/0.96  --qbf_sk_in                             false
% 2.74/0.96  --qbf_pred_elim                         true
% 2.74/0.96  --qbf_split                             512
% 2.74/0.96  
% 2.74/0.96  ------ BMC1 Options
% 2.74/0.96  
% 2.74/0.96  --bmc1_incremental                      false
% 2.74/0.96  --bmc1_axioms                           reachable_all
% 2.74/0.96  --bmc1_min_bound                        0
% 2.74/0.96  --bmc1_max_bound                        -1
% 2.74/0.96  --bmc1_max_bound_default                -1
% 2.74/0.96  --bmc1_symbol_reachability              true
% 2.74/0.96  --bmc1_property_lemmas                  false
% 2.74/0.96  --bmc1_k_induction                      false
% 2.74/0.96  --bmc1_non_equiv_states                 false
% 2.74/0.96  --bmc1_deadlock                         false
% 2.74/0.96  --bmc1_ucm                              false
% 2.74/0.96  --bmc1_add_unsat_core                   none
% 2.74/0.96  --bmc1_unsat_core_children              false
% 2.74/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.96  --bmc1_out_stat                         full
% 2.74/0.96  --bmc1_ground_init                      false
% 2.74/0.96  --bmc1_pre_inst_next_state              false
% 2.74/0.96  --bmc1_pre_inst_state                   false
% 2.74/0.96  --bmc1_pre_inst_reach_state             false
% 2.74/0.96  --bmc1_out_unsat_core                   false
% 2.74/0.96  --bmc1_aig_witness_out                  false
% 2.74/0.96  --bmc1_verbose                          false
% 2.74/0.96  --bmc1_dump_clauses_tptp                false
% 2.74/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.96  --bmc1_dump_file                        -
% 2.74/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.96  --bmc1_ucm_extend_mode                  1
% 2.74/0.96  --bmc1_ucm_init_mode                    2
% 2.74/0.96  --bmc1_ucm_cone_mode                    none
% 2.74/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.96  --bmc1_ucm_relax_model                  4
% 2.74/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.96  --bmc1_ucm_layered_model                none
% 2.74/0.96  --bmc1_ucm_max_lemma_size               10
% 2.74/0.96  
% 2.74/0.96  ------ AIG Options
% 2.74/0.96  
% 2.74/0.96  --aig_mode                              false
% 2.74/0.96  
% 2.74/0.96  ------ Instantiation Options
% 2.74/0.96  
% 2.74/0.96  --instantiation_flag                    true
% 2.74/0.96  --inst_sos_flag                         false
% 2.74/0.96  --inst_sos_phase                        true
% 2.74/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.96  --inst_lit_sel_side                     num_symb
% 2.74/0.96  --inst_solver_per_active                1400
% 2.74/0.96  --inst_solver_calls_frac                1.
% 2.74/0.96  --inst_passive_queue_type               priority_queues
% 2.74/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.96  --inst_passive_queues_freq              [25;2]
% 2.74/0.96  --inst_dismatching                      true
% 2.74/0.96  --inst_eager_unprocessed_to_passive     true
% 2.74/0.96  --inst_prop_sim_given                   true
% 2.74/0.96  --inst_prop_sim_new                     false
% 2.74/0.96  --inst_subs_new                         false
% 2.74/0.96  --inst_eq_res_simp                      false
% 2.74/0.96  --inst_subs_given                       false
% 2.74/0.96  --inst_orphan_elimination               true
% 2.74/0.96  --inst_learning_loop_flag               true
% 2.74/0.96  --inst_learning_start                   3000
% 2.74/0.96  --inst_learning_factor                  2
% 2.74/0.96  --inst_start_prop_sim_after_learn       3
% 2.74/0.96  --inst_sel_renew                        solver
% 2.74/0.96  --inst_lit_activity_flag                true
% 2.74/0.96  --inst_restr_to_given                   false
% 2.74/0.96  --inst_activity_threshold               500
% 2.74/0.96  --inst_out_proof                        true
% 2.74/0.96  
% 2.74/0.96  ------ Resolution Options
% 2.74/0.96  
% 2.74/0.96  --resolution_flag                       true
% 2.74/0.96  --res_lit_sel                           adaptive
% 2.74/0.96  --res_lit_sel_side                      none
% 2.74/0.96  --res_ordering                          kbo
% 2.74/0.96  --res_to_prop_solver                    active
% 2.74/0.96  --res_prop_simpl_new                    false
% 2.74/0.96  --res_prop_simpl_given                  true
% 2.74/0.96  --res_passive_queue_type                priority_queues
% 2.74/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.96  --res_passive_queues_freq               [15;5]
% 2.74/0.96  --res_forward_subs                      full
% 2.74/0.96  --res_backward_subs                     full
% 2.74/0.96  --res_forward_subs_resolution           true
% 2.74/0.96  --res_backward_subs_resolution          true
% 2.74/0.96  --res_orphan_elimination                true
% 2.74/0.96  --res_time_limit                        2.
% 2.74/0.96  --res_out_proof                         true
% 2.74/0.96  
% 2.74/0.96  ------ Superposition Options
% 2.74/0.96  
% 2.74/0.96  --superposition_flag                    true
% 2.74/0.96  --sup_passive_queue_type                priority_queues
% 2.74/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.96  --demod_completeness_check              fast
% 2.74/0.96  --demod_use_ground                      true
% 2.74/0.96  --sup_to_prop_solver                    passive
% 2.74/0.96  --sup_prop_simpl_new                    true
% 2.74/0.96  --sup_prop_simpl_given                  true
% 2.74/0.96  --sup_fun_splitting                     false
% 2.74/0.96  --sup_smt_interval                      50000
% 2.74/0.96  
% 2.74/0.96  ------ Superposition Simplification Setup
% 2.74/0.96  
% 2.74/0.96  --sup_indices_passive                   []
% 2.74/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_full_bw                           [BwDemod]
% 2.74/0.96  --sup_immed_triv                        [TrivRules]
% 2.74/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_immed_bw_main                     []
% 2.74/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.96  
% 2.74/0.96  ------ Combination Options
% 2.74/0.96  
% 2.74/0.96  --comb_res_mult                         3
% 2.74/0.96  --comb_sup_mult                         2
% 2.74/0.96  --comb_inst_mult                        10
% 2.74/0.96  
% 2.74/0.96  ------ Debug Options
% 2.74/0.96  
% 2.74/0.96  --dbg_backtrace                         false
% 2.74/0.96  --dbg_dump_prop_clauses                 false
% 2.74/0.96  --dbg_dump_prop_clauses_file            -
% 2.74/0.96  --dbg_out_stat                          false
% 2.74/0.96  ------ Parsing...
% 2.74/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.96  ------ Proving...
% 2.74/0.96  ------ Problem Properties 
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  clauses                                 21
% 2.74/0.96  conjectures                             3
% 2.74/0.96  EPR                                     4
% 2.74/0.96  Horn                                    16
% 2.74/0.96  unary                                   10
% 2.74/0.96  binary                                  3
% 2.74/0.96  lits                                    41
% 2.74/0.96  lits eq                                 20
% 2.74/0.96  fd_pure                                 0
% 2.74/0.96  fd_pseudo                               0
% 2.74/0.96  fd_cond                                 0
% 2.74/0.96  fd_pseudo_cond                          5
% 2.74/0.96  AC symbols                              0
% 2.74/0.96  
% 2.74/0.96  ------ Schedule dynamic 5 is on 
% 2.74/0.96  
% 2.74/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  ------ 
% 2.74/0.96  Current options:
% 2.74/0.96  ------ 
% 2.74/0.96  
% 2.74/0.96  ------ Input Options
% 2.74/0.96  
% 2.74/0.96  --out_options                           all
% 2.74/0.96  --tptp_safe_out                         true
% 2.74/0.96  --problem_path                          ""
% 2.74/0.96  --include_path                          ""
% 2.74/0.96  --clausifier                            res/vclausify_rel
% 2.74/0.96  --clausifier_options                    --mode clausify
% 2.74/0.96  --stdin                                 false
% 2.74/0.96  --stats_out                             all
% 2.74/0.96  
% 2.74/0.96  ------ General Options
% 2.74/0.96  
% 2.74/0.96  --fof                                   false
% 2.74/0.96  --time_out_real                         305.
% 2.74/0.96  --time_out_virtual                      -1.
% 2.74/0.96  --symbol_type_check                     false
% 2.74/0.96  --clausify_out                          false
% 2.74/0.96  --sig_cnt_out                           false
% 2.74/0.96  --trig_cnt_out                          false
% 2.74/0.96  --trig_cnt_out_tolerance                1.
% 2.74/0.96  --trig_cnt_out_sk_spl                   false
% 2.74/0.96  --abstr_cl_out                          false
% 2.74/0.96  
% 2.74/0.96  ------ Global Options
% 2.74/0.96  
% 2.74/0.96  --schedule                              default
% 2.74/0.96  --add_important_lit                     false
% 2.74/0.96  --prop_solver_per_cl                    1000
% 2.74/0.96  --min_unsat_core                        false
% 2.74/0.96  --soft_assumptions                      false
% 2.74/0.96  --soft_lemma_size                       3
% 2.74/0.96  --prop_impl_unit_size                   0
% 2.74/0.96  --prop_impl_unit                        []
% 2.74/0.96  --share_sel_clauses                     true
% 2.74/0.96  --reset_solvers                         false
% 2.74/0.96  --bc_imp_inh                            [conj_cone]
% 2.74/0.96  --conj_cone_tolerance                   3.
% 2.74/0.96  --extra_neg_conj                        none
% 2.74/0.96  --large_theory_mode                     true
% 2.74/0.96  --prolific_symb_bound                   200
% 2.74/0.96  --lt_threshold                          2000
% 2.74/0.96  --clause_weak_htbl                      true
% 2.74/0.96  --gc_record_bc_elim                     false
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing Options
% 2.74/0.96  
% 2.74/0.96  --preprocessing_flag                    true
% 2.74/0.96  --time_out_prep_mult                    0.1
% 2.74/0.96  --splitting_mode                        input
% 2.74/0.96  --splitting_grd                         true
% 2.74/0.96  --splitting_cvd                         false
% 2.74/0.96  --splitting_cvd_svl                     false
% 2.74/0.96  --splitting_nvd                         32
% 2.74/0.96  --sub_typing                            true
% 2.74/0.96  --prep_gs_sim                           true
% 2.74/0.96  --prep_unflatten                        true
% 2.74/0.96  --prep_res_sim                          true
% 2.74/0.96  --prep_upred                            true
% 2.74/0.96  --prep_sem_filter                       exhaustive
% 2.74/0.96  --prep_sem_filter_out                   false
% 2.74/0.96  --pred_elim                             true
% 2.74/0.96  --res_sim_input                         true
% 2.74/0.96  --eq_ax_congr_red                       true
% 2.74/0.96  --pure_diseq_elim                       true
% 2.74/0.96  --brand_transform                       false
% 2.74/0.96  --non_eq_to_eq                          false
% 2.74/0.96  --prep_def_merge                        true
% 2.74/0.96  --prep_def_merge_prop_impl              false
% 2.74/0.96  --prep_def_merge_mbd                    true
% 2.74/0.96  --prep_def_merge_tr_red                 false
% 2.74/0.96  --prep_def_merge_tr_cl                  false
% 2.74/0.96  --smt_preprocessing                     true
% 2.74/0.96  --smt_ac_axioms                         fast
% 2.74/0.96  --preprocessed_out                      false
% 2.74/0.96  --preprocessed_stats                    false
% 2.74/0.96  
% 2.74/0.96  ------ Abstraction refinement Options
% 2.74/0.96  
% 2.74/0.96  --abstr_ref                             []
% 2.74/0.96  --abstr_ref_prep                        false
% 2.74/0.96  --abstr_ref_until_sat                   false
% 2.74/0.96  --abstr_ref_sig_restrict                funpre
% 2.74/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.96  --abstr_ref_under                       []
% 2.74/0.96  
% 2.74/0.96  ------ SAT Options
% 2.74/0.96  
% 2.74/0.96  --sat_mode                              false
% 2.74/0.96  --sat_fm_restart_options                ""
% 2.74/0.96  --sat_gr_def                            false
% 2.74/0.96  --sat_epr_types                         true
% 2.74/0.96  --sat_non_cyclic_types                  false
% 2.74/0.96  --sat_finite_models                     false
% 2.74/0.96  --sat_fm_lemmas                         false
% 2.74/0.96  --sat_fm_prep                           false
% 2.74/0.96  --sat_fm_uc_incr                        true
% 2.74/0.96  --sat_out_model                         small
% 2.74/0.96  --sat_out_clauses                       false
% 2.74/0.96  
% 2.74/0.96  ------ QBF Options
% 2.74/0.96  
% 2.74/0.96  --qbf_mode                              false
% 2.74/0.96  --qbf_elim_univ                         false
% 2.74/0.96  --qbf_dom_inst                          none
% 2.74/0.96  --qbf_dom_pre_inst                      false
% 2.74/0.96  --qbf_sk_in                             false
% 2.74/0.96  --qbf_pred_elim                         true
% 2.74/0.96  --qbf_split                             512
% 2.74/0.96  
% 2.74/0.96  ------ BMC1 Options
% 2.74/0.96  
% 2.74/0.96  --bmc1_incremental                      false
% 2.74/0.96  --bmc1_axioms                           reachable_all
% 2.74/0.96  --bmc1_min_bound                        0
% 2.74/0.96  --bmc1_max_bound                        -1
% 2.74/0.96  --bmc1_max_bound_default                -1
% 2.74/0.96  --bmc1_symbol_reachability              true
% 2.74/0.96  --bmc1_property_lemmas                  false
% 2.74/0.96  --bmc1_k_induction                      false
% 2.74/0.96  --bmc1_non_equiv_states                 false
% 2.74/0.96  --bmc1_deadlock                         false
% 2.74/0.96  --bmc1_ucm                              false
% 2.74/0.96  --bmc1_add_unsat_core                   none
% 2.74/0.96  --bmc1_unsat_core_children              false
% 2.74/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.96  --bmc1_out_stat                         full
% 2.74/0.96  --bmc1_ground_init                      false
% 2.74/0.96  --bmc1_pre_inst_next_state              false
% 2.74/0.96  --bmc1_pre_inst_state                   false
% 2.74/0.96  --bmc1_pre_inst_reach_state             false
% 2.74/0.96  --bmc1_out_unsat_core                   false
% 2.74/0.96  --bmc1_aig_witness_out                  false
% 2.74/0.96  --bmc1_verbose                          false
% 2.74/0.96  --bmc1_dump_clauses_tptp                false
% 2.74/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.96  --bmc1_dump_file                        -
% 2.74/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.96  --bmc1_ucm_extend_mode                  1
% 2.74/0.96  --bmc1_ucm_init_mode                    2
% 2.74/0.96  --bmc1_ucm_cone_mode                    none
% 2.74/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.96  --bmc1_ucm_relax_model                  4
% 2.74/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.96  --bmc1_ucm_layered_model                none
% 2.74/0.96  --bmc1_ucm_max_lemma_size               10
% 2.74/0.96  
% 2.74/0.96  ------ AIG Options
% 2.74/0.96  
% 2.74/0.96  --aig_mode                              false
% 2.74/0.96  
% 2.74/0.96  ------ Instantiation Options
% 2.74/0.96  
% 2.74/0.96  --instantiation_flag                    true
% 2.74/0.96  --inst_sos_flag                         false
% 2.74/0.96  --inst_sos_phase                        true
% 2.74/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.96  --inst_lit_sel_side                     none
% 2.74/0.96  --inst_solver_per_active                1400
% 2.74/0.96  --inst_solver_calls_frac                1.
% 2.74/0.96  --inst_passive_queue_type               priority_queues
% 2.74/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.96  --inst_passive_queues_freq              [25;2]
% 2.74/0.96  --inst_dismatching                      true
% 2.74/0.96  --inst_eager_unprocessed_to_passive     true
% 2.74/0.96  --inst_prop_sim_given                   true
% 2.74/0.96  --inst_prop_sim_new                     false
% 2.74/0.96  --inst_subs_new                         false
% 2.74/0.96  --inst_eq_res_simp                      false
% 2.74/0.96  --inst_subs_given                       false
% 2.74/0.96  --inst_orphan_elimination               true
% 2.74/0.96  --inst_learning_loop_flag               true
% 2.74/0.96  --inst_learning_start                   3000
% 2.74/0.96  --inst_learning_factor                  2
% 2.74/0.96  --inst_start_prop_sim_after_learn       3
% 2.74/0.96  --inst_sel_renew                        solver
% 2.74/0.96  --inst_lit_activity_flag                true
% 2.74/0.96  --inst_restr_to_given                   false
% 2.74/0.96  --inst_activity_threshold               500
% 2.74/0.96  --inst_out_proof                        true
% 2.74/0.96  
% 2.74/0.96  ------ Resolution Options
% 2.74/0.96  
% 2.74/0.96  --resolution_flag                       false
% 2.74/0.96  --res_lit_sel                           adaptive
% 2.74/0.96  --res_lit_sel_side                      none
% 2.74/0.96  --res_ordering                          kbo
% 2.74/0.96  --res_to_prop_solver                    active
% 2.74/0.96  --res_prop_simpl_new                    false
% 2.74/0.96  --res_prop_simpl_given                  true
% 2.74/0.96  --res_passive_queue_type                priority_queues
% 2.74/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.96  --res_passive_queues_freq               [15;5]
% 2.74/0.96  --res_forward_subs                      full
% 2.74/0.96  --res_backward_subs                     full
% 2.74/0.96  --res_forward_subs_resolution           true
% 2.74/0.96  --res_backward_subs_resolution          true
% 2.74/0.96  --res_orphan_elimination                true
% 2.74/0.96  --res_time_limit                        2.
% 2.74/0.96  --res_out_proof                         true
% 2.74/0.96  
% 2.74/0.96  ------ Superposition Options
% 2.74/0.96  
% 2.74/0.96  --superposition_flag                    true
% 2.74/0.96  --sup_passive_queue_type                priority_queues
% 2.74/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.96  --demod_completeness_check              fast
% 2.74/0.96  --demod_use_ground                      true
% 2.74/0.96  --sup_to_prop_solver                    passive
% 2.74/0.96  --sup_prop_simpl_new                    true
% 2.74/0.96  --sup_prop_simpl_given                  true
% 2.74/0.96  --sup_fun_splitting                     false
% 2.74/0.96  --sup_smt_interval                      50000
% 2.74/0.96  
% 2.74/0.96  ------ Superposition Simplification Setup
% 2.74/0.96  
% 2.74/0.96  --sup_indices_passive                   []
% 2.74/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_full_bw                           [BwDemod]
% 2.74/0.96  --sup_immed_triv                        [TrivRules]
% 2.74/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_immed_bw_main                     []
% 2.74/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.96  
% 2.74/0.96  ------ Combination Options
% 2.74/0.96  
% 2.74/0.96  --comb_res_mult                         3
% 2.74/0.96  --comb_sup_mult                         2
% 2.74/0.96  --comb_inst_mult                        10
% 2.74/0.96  
% 2.74/0.96  ------ Debug Options
% 2.74/0.96  
% 2.74/0.96  --dbg_backtrace                         false
% 2.74/0.96  --dbg_dump_prop_clauses                 false
% 2.74/0.96  --dbg_dump_prop_clauses_file            -
% 2.74/0.96  --dbg_out_stat                          false
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  ------ Proving...
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  % SZS status Theorem for theBenchmark.p
% 2.74/0.96  
% 2.74/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.96  
% 2.74/0.96  fof(f14,conjecture,(
% 2.74/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f15,negated_conjecture,(
% 2.74/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.74/0.96    inference(negated_conjecture,[],[f14])).
% 2.74/0.96  
% 2.74/0.96  fof(f27,plain,(
% 2.74/0.96    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.74/0.96    inference(ennf_transformation,[],[f15])).
% 2.74/0.96  
% 2.74/0.96  fof(f28,plain,(
% 2.74/0.96    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.74/0.96    inference(flattening,[],[f27])).
% 2.74/0.96  
% 2.74/0.96  fof(f39,plain,(
% 2.74/0.96    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 2.74/0.96    introduced(choice_axiom,[])).
% 2.74/0.96  
% 2.74/0.96  fof(f40,plain,(
% 2.74/0.96    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 2.74/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39])).
% 2.74/0.96  
% 2.74/0.96  fof(f70,plain,(
% 2.74/0.96    r2_hidden(sK4,sK2)),
% 2.74/0.96    inference(cnf_transformation,[],[f40])).
% 2.74/0.96  
% 2.74/0.96  fof(f13,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f25,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(ennf_transformation,[],[f13])).
% 2.74/0.96  
% 2.74/0.96  fof(f26,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(flattening,[],[f25])).
% 2.74/0.96  
% 2.74/0.96  fof(f38,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(nnf_transformation,[],[f26])).
% 2.74/0.96  
% 2.74/0.96  fof(f61,plain,(
% 2.74/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.96    inference(cnf_transformation,[],[f38])).
% 2.74/0.96  
% 2.74/0.96  fof(f68,plain,(
% 2.74/0.96    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 2.74/0.96    inference(cnf_transformation,[],[f40])).
% 2.74/0.96  
% 2.74/0.96  fof(f4,axiom,(
% 2.74/0.96    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f52,plain,(
% 2.74/0.96    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f4])).
% 2.74/0.96  
% 2.74/0.96  fof(f5,axiom,(
% 2.74/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f53,plain,(
% 2.74/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f5])).
% 2.74/0.96  
% 2.74/0.96  fof(f72,plain,(
% 2.74/0.96    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.74/0.96    inference(definition_unfolding,[],[f52,f53])).
% 2.74/0.96  
% 2.74/0.96  fof(f85,plain,(
% 2.74/0.96    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3))),
% 2.74/0.96    inference(definition_unfolding,[],[f68,f72])).
% 2.74/0.96  
% 2.74/0.96  fof(f69,plain,(
% 2.74/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 2.74/0.96    inference(cnf_transformation,[],[f40])).
% 2.74/0.96  
% 2.74/0.96  fof(f84,plain,(
% 2.74/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))),
% 2.74/0.96    inference(definition_unfolding,[],[f69,f72])).
% 2.74/0.96  
% 2.74/0.96  fof(f12,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f24,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(ennf_transformation,[],[f12])).
% 2.74/0.96  
% 2.74/0.96  fof(f60,plain,(
% 2.74/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.96    inference(cnf_transformation,[],[f24])).
% 2.74/0.96  
% 2.74/0.96  fof(f3,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f33,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.74/0.96    inference(nnf_transformation,[],[f3])).
% 2.74/0.96  
% 2.74/0.96  fof(f34,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.74/0.96    inference(flattening,[],[f33])).
% 2.74/0.96  
% 2.74/0.96  fof(f35,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.74/0.96    inference(rectify,[],[f34])).
% 2.74/0.96  
% 2.74/0.96  fof(f36,plain,(
% 2.74/0.96    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.74/0.96    introduced(choice_axiom,[])).
% 2.74/0.96  
% 2.74/0.96  fof(f37,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.74/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.74/0.96  
% 2.74/0.96  fof(f48,plain,(
% 2.74/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.74/0.96    inference(cnf_transformation,[],[f37])).
% 2.74/0.96  
% 2.74/0.96  fof(f80,plain,(
% 2.74/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.74/0.96    inference(definition_unfolding,[],[f48,f53])).
% 2.74/0.96  
% 2.74/0.96  fof(f89,plain,(
% 2.74/0.96    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 2.74/0.96    inference(equality_resolution,[],[f80])).
% 2.74/0.96  
% 2.74/0.96  fof(f90,plain,(
% 2.74/0.96    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 2.74/0.96    inference(equality_resolution,[],[f89])).
% 2.74/0.96  
% 2.74/0.96  fof(f1,axiom,(
% 2.74/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f41,plain,(
% 2.74/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f1])).
% 2.74/0.96  
% 2.74/0.96  fof(f9,axiom,(
% 2.74/0.96    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f21,plain,(
% 2.74/0.96    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.74/0.96    inference(ennf_transformation,[],[f9])).
% 2.74/0.96  
% 2.74/0.96  fof(f57,plain,(
% 2.74/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f21])).
% 2.74/0.96  
% 2.74/0.96  fof(f11,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f16,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.74/0.96    inference(pure_predicate_removal,[],[f11])).
% 2.74/0.96  
% 2.74/0.96  fof(f23,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(ennf_transformation,[],[f16])).
% 2.74/0.96  
% 2.74/0.96  fof(f59,plain,(
% 2.74/0.96    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.96    inference(cnf_transformation,[],[f23])).
% 2.74/0.96  
% 2.74/0.96  fof(f8,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f19,plain,(
% 2.74/0.96    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.74/0.96    inference(ennf_transformation,[],[f8])).
% 2.74/0.96  
% 2.74/0.96  fof(f20,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.74/0.96    inference(flattening,[],[f19])).
% 2.74/0.96  
% 2.74/0.96  fof(f56,plain,(
% 2.74/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f20])).
% 2.74/0.96  
% 2.74/0.96  fof(f67,plain,(
% 2.74/0.96    v1_funct_1(sK5)),
% 2.74/0.96    inference(cnf_transformation,[],[f40])).
% 2.74/0.96  
% 2.74/0.96  fof(f10,axiom,(
% 2.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f22,plain,(
% 2.74/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.96    inference(ennf_transformation,[],[f10])).
% 2.74/0.96  
% 2.74/0.96  fof(f58,plain,(
% 2.74/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.96    inference(cnf_transformation,[],[f22])).
% 2.74/0.96  
% 2.74/0.96  fof(f7,axiom,(
% 2.74/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f17,plain,(
% 2.74/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.74/0.96    inference(ennf_transformation,[],[f7])).
% 2.74/0.96  
% 2.74/0.96  fof(f18,plain,(
% 2.74/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.74/0.96    inference(flattening,[],[f17])).
% 2.74/0.96  
% 2.74/0.96  fof(f55,plain,(
% 2.74/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.74/0.96    inference(cnf_transformation,[],[f18])).
% 2.74/0.96  
% 2.74/0.96  fof(f6,axiom,(
% 2.74/0.96    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f54,plain,(
% 2.74/0.96    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.74/0.96    inference(cnf_transformation,[],[f6])).
% 2.74/0.96  
% 2.74/0.96  fof(f83,plain,(
% 2.74/0.96    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 2.74/0.96    inference(definition_unfolding,[],[f54,f72])).
% 2.74/0.96  
% 2.74/0.96  fof(f2,axiom,(
% 2.74/0.96    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.96  
% 2.74/0.96  fof(f29,plain,(
% 2.74/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.96    inference(nnf_transformation,[],[f2])).
% 2.74/0.96  
% 2.74/0.96  fof(f30,plain,(
% 2.74/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.96    inference(rectify,[],[f29])).
% 2.74/0.96  
% 2.74/0.96  fof(f31,plain,(
% 2.74/0.96    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.74/0.96    introduced(choice_axiom,[])).
% 2.74/0.96  
% 2.74/0.96  fof(f32,plain,(
% 2.74/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.74/0.96  
% 2.74/0.96  fof(f42,plain,(
% 2.74/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.74/0.96    inference(cnf_transformation,[],[f32])).
% 2.74/0.96  
% 2.74/0.96  fof(f76,plain,(
% 2.74/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 2.74/0.96    inference(definition_unfolding,[],[f42,f72])).
% 2.74/0.96  
% 2.74/0.96  fof(f88,plain,(
% 2.74/0.96    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 2.74/0.96    inference(equality_resolution,[],[f76])).
% 2.74/0.96  
% 2.74/0.96  fof(f71,plain,(
% 2.74/0.96    k1_funct_1(sK5,sK4) != sK3),
% 2.74/0.96    inference(cnf_transformation,[],[f40])).
% 2.74/0.96  
% 2.74/0.96  cnf(c_25,negated_conjecture,
% 2.74/0.96      ( r2_hidden(sK4,sK2) ),
% 2.74/0.96      inference(cnf_transformation,[],[f70]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2251,plain,
% 2.74/0.96      ( r2_hidden(sK4,sK2) = iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_23,plain,
% 2.74/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.96      | k1_xboole_0 = X2 ),
% 2.74/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_27,negated_conjecture,
% 2.74/0.96      ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
% 2.74/0.96      inference(cnf_transformation,[],[f85]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_427,plain,
% 2.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.96      | k1_enumset1(sK3,sK3,sK3) != X2
% 2.74/0.96      | sK2 != X1
% 2.74/0.96      | sK5 != X0
% 2.74/0.96      | k1_xboole_0 = X2 ),
% 2.74/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_428,plain,
% 2.74/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
% 2.74/0.96      | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 2.74/0.96      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 2.74/0.96      inference(unflattening,[status(thm)],[c_427]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_26,negated_conjecture,
% 2.74/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
% 2.74/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_430,plain,
% 2.74/0.96      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 2.74/0.96      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 2.74/0.96      inference(global_propositional_subsumption,
% 2.74/0.96                [status(thm)],
% 2.74/0.96                [c_428,c_26]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2250,plain,
% 2.74/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_17,plain,
% 2.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.74/0.96      inference(cnf_transformation,[],[f60]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2252,plain,
% 2.74/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.74/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2929,plain,
% 2.74/0.96      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_2250,c_2252]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_3027,plain,
% 2.74/0.96      ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0 | k1_relat_1(sK5) = sK2 ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_430,c_2929]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_8,plain,
% 2.74/0.96      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 2.74/0.96      inference(cnf_transformation,[],[f90]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_0,plain,
% 2.74/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 2.74/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_14,plain,
% 2.74/0.96      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.74/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_312,plain,
% 2.74/0.96      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.74/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_313,plain,
% 2.74/0.96      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.74/0.96      inference(unflattening,[status(thm)],[c_312]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_912,plain,
% 2.74/0.96      ( X0 != X1 | k1_enumset1(X2,X2,X1) != k1_xboole_0 ),
% 2.74/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_313]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_913,plain,
% 2.74/0.96      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 2.74/0.96      inference(unflattening,[status(thm)],[c_912]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_3031,plain,
% 2.74/0.96      ( k1_relat_1(sK5) = sK2 ),
% 2.74/0.96      inference(forward_subsumption_resolution,
% 2.74/0.96                [status(thm)],
% 2.74/0.96                [c_3027,c_913]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_16,plain,
% 2.74/0.96      ( v5_relat_1(X0,X1)
% 2.74/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.74/0.96      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_13,plain,
% 2.74/0.96      ( ~ v5_relat_1(X0,X1)
% 2.74/0.96      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.74/0.96      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.74/0.96      | ~ v1_relat_1(X0)
% 2.74/0.96      | ~ v1_funct_1(X0) ),
% 2.74/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_28,negated_conjecture,
% 2.74/0.96      ( v1_funct_1(sK5) ),
% 2.74/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_335,plain,
% 2.74/0.96      ( ~ v5_relat_1(X0,X1)
% 2.74/0.96      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.74/0.96      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.74/0.96      | ~ v1_relat_1(X0)
% 2.74/0.96      | sK5 != X0 ),
% 2.74/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_336,plain,
% 2.74/0.96      ( ~ v5_relat_1(sK5,X0)
% 2.74/0.96      | m1_subset_1(k1_funct_1(sK5,X1),X0)
% 2.74/0.96      | ~ r2_hidden(X1,k1_relat_1(sK5))
% 2.74/0.96      | ~ v1_relat_1(sK5) ),
% 2.74/0.96      inference(unflattening,[status(thm)],[c_335]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_358,plain,
% 2.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.96      | m1_subset_1(k1_funct_1(sK5,X3),X4)
% 2.74/0.96      | ~ r2_hidden(X3,k1_relat_1(sK5))
% 2.74/0.96      | ~ v1_relat_1(sK5)
% 2.74/0.96      | X4 != X2
% 2.74/0.96      | sK5 != X0 ),
% 2.74/0.96      inference(resolution_lifted,[status(thm)],[c_16,c_336]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_359,plain,
% 2.74/0.96      ( m1_subset_1(k1_funct_1(sK5,X0),X1)
% 2.74/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/0.96      | ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.74/0.96      | ~ v1_relat_1(sK5) ),
% 2.74/0.96      inference(unflattening,[status(thm)],[c_358]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_15,plain,
% 2.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.96      | v1_relat_1(X0) ),
% 2.74/0.96      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_371,plain,
% 2.74/0.96      ( m1_subset_1(k1_funct_1(sK5,X0),X1)
% 2.74/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/0.96      | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 2.74/0.96      inference(forward_subsumption_resolution,
% 2.74/0.96                [status(thm)],
% 2.74/0.96                [c_359,c_15]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2248,plain,
% 2.74/0.96      ( m1_subset_1(k1_funct_1(sK5,X0),X1) = iProver_top
% 2.74/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.74/0.96      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2446,plain,
% 2.74/0.96      ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.74/0.96      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_2250,c_2248]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_3033,plain,
% 2.74/0.96      ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.74/0.96      | r2_hidden(X0,sK2) != iProver_top ),
% 2.74/0.96      inference(demodulation,[status(thm)],[c_3031,c_2446]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_12,plain,
% 2.74/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.74/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2253,plain,
% 2.74/0.96      ( m1_subset_1(X0,X1) != iProver_top
% 2.74/0.96      | r2_hidden(X0,X1) = iProver_top
% 2.74/0.96      | v1_xboole_0(X1) = iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_3382,plain,
% 2.74/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 2.74/0.96      | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.74/0.96      | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_3033,c_2253]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_11,plain,
% 2.74/0.96      ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
% 2.74/0.96      inference(cnf_transformation,[],[f83]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2254,plain,
% 2.74/0.96      ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_4052,plain,
% 2.74/0.96      ( r2_hidden(X0,sK2) != iProver_top
% 2.74/0.96      | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 2.74/0.96      inference(forward_subsumption_resolution,
% 2.74/0.96                [status(thm)],
% 2.74/0.96                [c_3382,c_2254]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_4,plain,
% 2.74/0.96      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 2.74/0.96      inference(cnf_transformation,[],[f88]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_2261,plain,
% 2.74/0.96      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 2.74/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_4056,plain,
% 2.74/0.96      ( k1_funct_1(sK5,X0) = sK3 | r2_hidden(X0,sK2) != iProver_top ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_4052,c_2261]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_4065,plain,
% 2.74/0.96      ( k1_funct_1(sK5,sK4) = sK3 ),
% 2.74/0.96      inference(superposition,[status(thm)],[c_2251,c_4056]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(c_24,negated_conjecture,
% 2.74/0.96      ( k1_funct_1(sK5,sK4) != sK3 ),
% 2.74/0.96      inference(cnf_transformation,[],[f71]) ).
% 2.74/0.96  
% 2.74/0.96  cnf(contradiction,plain,
% 2.74/0.96      ( $false ),
% 2.74/0.96      inference(minisat,[status(thm)],[c_4065,c_24]) ).
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.96  
% 2.74/0.96  ------                               Statistics
% 2.74/0.96  
% 2.74/0.96  ------ General
% 2.74/0.96  
% 2.74/0.96  abstr_ref_over_cycles:                  0
% 2.74/0.96  abstr_ref_under_cycles:                 0
% 2.74/0.96  gc_basic_clause_elim:                   0
% 2.74/0.96  forced_gc_time:                         0
% 2.74/0.96  parsing_time:                           0.009
% 2.74/0.96  unif_index_cands_time:                  0.
% 2.74/0.96  unif_index_add_time:                    0.
% 2.74/0.96  orderings_time:                         0.
% 2.74/0.96  out_proof_time:                         0.009
% 2.74/0.96  total_time:                             0.15
% 2.74/0.96  num_of_symbols:                         52
% 2.74/0.96  num_of_terms:                           3973
% 2.74/0.96  
% 2.74/0.96  ------ Preprocessing
% 2.74/0.96  
% 2.74/0.96  num_of_splits:                          0
% 2.74/0.96  num_of_split_atoms:                     0
% 2.74/0.96  num_of_reused_defs:                     0
% 2.74/0.96  num_eq_ax_congr_red:                    22
% 2.74/0.96  num_of_sem_filtered_clauses:            1
% 2.74/0.96  num_of_subtypes:                        0
% 2.74/0.96  monotx_restored_types:                  0
% 2.74/0.96  sat_num_of_epr_types:                   0
% 2.74/0.96  sat_num_of_non_cyclic_types:            0
% 2.74/0.96  sat_guarded_non_collapsed_types:        0
% 2.74/0.96  num_pure_diseq_elim:                    0
% 2.74/0.96  simp_replaced_by:                       0
% 2.74/0.96  res_preprocessed:                       115
% 2.74/0.96  prep_upred:                             0
% 2.74/0.96  prep_unflattend:                        156
% 2.74/0.96  smt_new_axioms:                         0
% 2.74/0.96  pred_elim_cands:                        3
% 2.74/0.96  pred_elim:                              5
% 2.74/0.96  pred_elim_cl:                           8
% 2.74/0.96  pred_elim_cycles:                       10
% 2.74/0.96  merged_defs:                            0
% 2.74/0.96  merged_defs_ncl:                        0
% 2.74/0.96  bin_hyper_res:                          0
% 2.74/0.96  prep_cycles:                            4
% 2.74/0.96  pred_elim_time:                         0.031
% 2.74/0.96  splitting_time:                         0.
% 2.74/0.96  sem_filter_time:                        0.
% 2.74/0.96  monotx_time:                            0.
% 2.74/0.96  subtype_inf_time:                       0.
% 2.74/0.96  
% 2.74/0.96  ------ Problem properties
% 2.74/0.96  
% 2.74/0.96  clauses:                                21
% 2.74/0.96  conjectures:                            3
% 2.74/0.96  epr:                                    4
% 2.74/0.96  horn:                                   16
% 2.74/0.96  ground:                                 5
% 2.74/0.96  unary:                                  10
% 2.74/0.96  binary:                                 3
% 2.74/0.96  lits:                                   41
% 2.74/0.96  lits_eq:                                20
% 2.74/0.96  fd_pure:                                0
% 2.74/0.96  fd_pseudo:                              0
% 2.74/0.96  fd_cond:                                0
% 2.74/0.96  fd_pseudo_cond:                         5
% 2.74/0.96  ac_symbols:                             0
% 2.74/0.96  
% 2.74/0.96  ------ Propositional Solver
% 2.74/0.96  
% 2.74/0.96  prop_solver_calls:                      26
% 2.74/0.96  prop_fast_solver_calls:                 885
% 2.74/0.96  smt_solver_calls:                       0
% 2.74/0.96  smt_fast_solver_calls:                  0
% 2.74/0.96  prop_num_of_clauses:                    1049
% 2.74/0.96  prop_preprocess_simplified:             5164
% 2.74/0.96  prop_fo_subsumed:                       4
% 2.74/0.96  prop_solver_time:                       0.
% 2.74/0.96  smt_solver_time:                        0.
% 2.74/0.96  smt_fast_solver_time:                   0.
% 2.74/0.96  prop_fast_solver_time:                  0.
% 2.74/0.96  prop_unsat_core_time:                   0.
% 2.74/0.96  
% 2.74/0.96  ------ QBF
% 2.74/0.96  
% 2.74/0.96  qbf_q_res:                              0
% 2.74/0.96  qbf_num_tautologies:                    0
% 2.74/0.96  qbf_prep_cycles:                        0
% 2.74/0.96  
% 2.74/0.96  ------ BMC1
% 2.74/0.96  
% 2.74/0.96  bmc1_current_bound:                     -1
% 2.74/0.96  bmc1_last_solved_bound:                 -1
% 2.74/0.96  bmc1_unsat_core_size:                   -1
% 2.74/0.96  bmc1_unsat_core_parents_size:           -1
% 2.74/0.96  bmc1_merge_next_fun:                    0
% 2.74/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.96  
% 2.74/0.96  ------ Instantiation
% 2.74/0.96  
% 2.74/0.96  inst_num_of_clauses:                    299
% 2.74/0.96  inst_num_in_passive:                    163
% 2.74/0.96  inst_num_in_active:                     136
% 2.74/0.96  inst_num_in_unprocessed:                0
% 2.74/0.96  inst_num_of_loops:                      140
% 2.74/0.96  inst_num_of_learning_restarts:          0
% 2.74/0.96  inst_num_moves_active_passive:          3
% 2.74/0.96  inst_lit_activity:                      0
% 2.74/0.96  inst_lit_activity_moves:                0
% 2.74/0.96  inst_num_tautologies:                   0
% 2.74/0.96  inst_num_prop_implied:                  0
% 2.74/0.96  inst_num_existing_simplified:           0
% 2.74/0.96  inst_num_eq_res_simplified:             0
% 2.74/0.96  inst_num_child_elim:                    0
% 2.74/0.96  inst_num_of_dismatching_blockings:      63
% 2.74/0.96  inst_num_of_non_proper_insts:           216
% 2.74/0.96  inst_num_of_duplicates:                 0
% 2.74/0.96  inst_inst_num_from_inst_to_res:         0
% 2.74/0.96  inst_dismatching_checking_time:         0.
% 2.74/0.96  
% 2.74/0.96  ------ Resolution
% 2.74/0.96  
% 2.74/0.96  res_num_of_clauses:                     0
% 2.74/0.96  res_num_in_passive:                     0
% 2.74/0.96  res_num_in_active:                      0
% 2.74/0.96  res_num_of_loops:                       119
% 2.74/0.96  res_forward_subset_subsumed:            90
% 2.74/0.96  res_backward_subset_subsumed:           0
% 2.74/0.96  res_forward_subsumed:                   1
% 2.74/0.96  res_backward_subsumed:                  13
% 2.74/0.96  res_forward_subsumption_resolution:     2
% 2.74/0.96  res_backward_subsumption_resolution:    2
% 2.74/0.96  res_clause_to_clause_subsumption:       301
% 2.74/0.96  res_orphan_elimination:                 0
% 2.74/0.96  res_tautology_del:                      29
% 2.74/0.96  res_num_eq_res_simplified:              0
% 2.74/0.96  res_num_sel_changes:                    0
% 2.74/0.96  res_moves_from_active_to_pass:          0
% 2.74/0.96  
% 2.74/0.96  ------ Superposition
% 2.74/0.96  
% 2.74/0.96  sup_time_total:                         0.
% 2.74/0.96  sup_time_generating:                    0.
% 2.74/0.96  sup_time_sim_full:                      0.
% 2.74/0.96  sup_time_sim_immed:                     0.
% 2.74/0.96  
% 2.74/0.96  sup_num_of_clauses:                     31
% 2.74/0.96  sup_num_in_active:                      24
% 2.74/0.96  sup_num_in_passive:                     7
% 2.74/0.96  sup_num_of_loops:                       27
% 2.74/0.96  sup_fw_superposition:                   12
% 2.74/0.96  sup_bw_superposition:                   6
% 2.74/0.96  sup_immediate_simplified:               1
% 2.74/0.96  sup_given_eliminated:                   0
% 2.74/0.96  comparisons_done:                       0
% 2.74/0.96  comparisons_avoided:                    2
% 2.74/0.96  
% 2.74/0.96  ------ Simplifications
% 2.74/0.96  
% 2.74/0.96  
% 2.74/0.96  sim_fw_subset_subsumed:                 1
% 2.74/0.96  sim_bw_subset_subsumed:                 1
% 2.74/0.96  sim_fw_subsumed:                        1
% 2.74/0.96  sim_bw_subsumed:                        0
% 2.74/0.96  sim_fw_subsumption_res:                 2
% 2.74/0.96  sim_bw_subsumption_res:                 0
% 2.74/0.96  sim_tautology_del:                      0
% 2.74/0.96  sim_eq_tautology_del:                   1
% 2.74/0.96  sim_eq_res_simp:                        0
% 2.74/0.96  sim_fw_demodulated:                     0
% 2.74/0.96  sim_bw_demodulated:                     3
% 2.74/0.96  sim_light_normalised:                   0
% 2.74/0.96  sim_joinable_taut:                      0
% 2.74/0.96  sim_joinable_simp:                      0
% 2.74/0.96  sim_ac_normalised:                      0
% 2.74/0.96  sim_smt_subsumption:                    0
% 2.74/0.96  
%------------------------------------------------------------------------------
