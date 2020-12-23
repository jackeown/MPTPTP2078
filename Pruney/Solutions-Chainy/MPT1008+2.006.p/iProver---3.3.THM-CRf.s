%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:05 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  168 (1198 expanded)
%              Number of clauses        :   84 ( 236 expanded)
%              Number of leaves         :   23 ( 324 expanded)
%              Depth                    :   22
%              Number of atoms          :  446 (2872 expanded)
%              Number of equality atoms :  230 (1583 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f100,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f67,f53,f53])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f49])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f81,f53])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f51])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f112,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f90,f91,f91,f53,f90])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f89,f91,f91])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f91,f91])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f53,f53])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f84,f53])).

fof(f86,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f113,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f88,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f88,f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f68,f53,f53])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f92,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f63,f53])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_26,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1500,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1499,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_9])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_347,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_21])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_1496,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1804,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_1496])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1515,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | o_0_0_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3397,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1804,c_1515])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1503,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2502,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1499,c_1503])).

cnf(c_3509,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3397,c_2502])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1706,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1749,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1040,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1743,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1849,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1743])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1780,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3681,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_3705,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3509,c_32,c_30,c_28,c_1706,c_1749,c_1849,c_3397,c_3681])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1511,plain,
    ( k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3711,plain,
    ( sK4 = o_0_0_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_1511])).

cnf(c_1813,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1039,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1869,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_2244,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2792,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_2793,plain,
    ( sK4 != sK4
    | sK4 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_3714,plain,
    ( sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_32,c_30,c_28,c_1706,c_1749,c_1813,c_1849,c_1869,c_2793,c_3397,c_3681])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X3
    | sK4 != X2
    | o_0_0_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ v1_funct_1(sK4)
    | o_0_0_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_29,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_327,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_32,c_30,c_29])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_1497,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1505,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2012,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4),k1_funct_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_1505])).

cnf(c_2598,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2502,c_2012])).

cnf(c_3721,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3714,c_2598])).

cnf(c_10,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3743,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3721,c_10])).

cnf(c_0,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1520,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4020,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3743,c_1520])).

cnf(c_4024,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1500,c_4020])).

cnf(c_1506,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4402,plain,
    ( k2_enumset1(k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2)) = k2_relat_1(X0)
    | k1_relat_1(X0) != o_0_0_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_1506])).

cnf(c_4463,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = k2_relat_1(o_0_0_xboole_0)
    | v1_funct_1(o_0_0_xboole_0) != iProver_top
    | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_4402])).

cnf(c_4495,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = o_0_0_xboole_0
    | v1_funct_1(o_0_0_xboole_0) != iProver_top
    | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4463,c_10])).

cnf(c_2600,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2502,c_28])).

cnf(c_3723,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != k2_relat_1(o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3714,c_2600])).

cnf(c_3734,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3723,c_10])).

cnf(c_6,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1832,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1835,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1832])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_1731,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(o_0_0_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_1707,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_1699,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1702,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_1698,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1700,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1698])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4509,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(grounding,[status(thm)],[c_1702:[bind(X1,$fot(o_0_0_xboole_0)),bind(X0,$fot(o_0_0_xboole_0))]])).

cnf(c_4510,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) != iProver_top
    | v1_relat_1(o_0_0_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_1700:[bind(X1,$fot(o_0_0_xboole_0)),bind(X0,$fot(o_0_0_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4495,c_3734,c_1835,c_1731,c_1707,c_4509,c_4510,c_35,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:22:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.18/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.98  
% 3.18/0.98  ------  iProver source info
% 3.18/0.98  
% 3.18/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.98  git: non_committed_changes: false
% 3.18/0.98  git: last_make_outside_of_git: false
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     num_symb
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       true
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  ------ Parsing...
% 3.18/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.98  ------ Proving...
% 3.18/0.98  ------ Problem Properties 
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  clauses                                 30
% 3.18/0.98  conjectures                             4
% 3.18/0.98  EPR                                     4
% 3.18/0.98  Horn                                    28
% 3.18/0.98  unary                                   15
% 3.18/0.98  binary                                  7
% 3.18/0.98  lits                                    57
% 3.18/0.98  lits eq                                 22
% 3.18/0.98  fd_pure                                 0
% 3.18/0.98  fd_pseudo                               0
% 3.18/0.98  fd_cond                                 5
% 3.18/0.98  fd_pseudo_cond                          1
% 3.18/0.98  AC symbols                              0
% 3.18/0.98  
% 3.18/0.98  ------ Schedule dynamic 5 is on 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  Current options:
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     none
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       false
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ Proving...
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  % SZS status Theorem for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  fof(f10,axiom,(
% 3.18/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f67,plain,(
% 3.18/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.18/0.98    inference(cnf_transformation,[],[f10])).
% 3.18/0.98  
% 3.18/0.98  fof(f1,axiom,(
% 3.18/0.98    k1_xboole_0 = o_0_0_xboole_0),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f53,plain,(
% 3.18/0.98    k1_xboole_0 = o_0_0_xboole_0),
% 3.18/0.98    inference(cnf_transformation,[],[f1])).
% 3.18/0.98  
% 3.18/0.98  fof(f100,plain,(
% 3.18/0.98    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 3.18/0.98    inference(definition_unfolding,[],[f67,f53,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f19,axiom,(
% 3.18/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f39,plain,(
% 3.18/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.18/0.98    inference(ennf_transformation,[],[f19])).
% 3.18/0.98  
% 3.18/0.98  fof(f49,plain,(
% 3.18/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f50,plain,(
% 3.18/0.98    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 3.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f49])).
% 3.18/0.98  
% 3.18/0.98  fof(f81,plain,(
% 3.18/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.18/0.98    inference(cnf_transformation,[],[f50])).
% 3.18/0.98  
% 3.18/0.98  fof(f108,plain,(
% 3.18/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0) )),
% 3.18/0.98    inference(definition_unfolding,[],[f81,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f21,conjecture,(
% 3.18/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f22,negated_conjecture,(
% 3.18/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.18/0.98    inference(negated_conjecture,[],[f21])).
% 3.18/0.98  
% 3.18/0.98  fof(f42,plain,(
% 3.18/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.18/0.98    inference(ennf_transformation,[],[f22])).
% 3.18/0.98  
% 3.18/0.98  fof(f43,plain,(
% 3.18/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.18/0.98    inference(flattening,[],[f42])).
% 3.18/0.98  
% 3.18/0.98  fof(f51,plain,(
% 3.18/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f52,plain,(
% 3.18/0.98    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 3.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f51])).
% 3.18/0.98  
% 3.18/0.98  fof(f87,plain,(
% 3.18/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 3.18/0.98    inference(cnf_transformation,[],[f52])).
% 3.18/0.98  
% 3.18/0.98  fof(f3,axiom,(
% 3.18/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f55,plain,(
% 3.18/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f3])).
% 3.18/0.98  
% 3.18/0.98  fof(f4,axiom,(
% 3.18/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f56,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f4])).
% 3.18/0.98  
% 3.18/0.98  fof(f5,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f57,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f5])).
% 3.18/0.98  
% 3.18/0.98  fof(f90,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f56,f57])).
% 3.18/0.98  
% 3.18/0.98  fof(f91,plain,(
% 3.18/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f55,f90])).
% 3.18/0.98  
% 3.18/0.98  fof(f112,plain,(
% 3.18/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 3.18/0.98    inference(definition_unfolding,[],[f87,f91])).
% 3.18/0.98  
% 3.18/0.98  fof(f17,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f23,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.18/0.98    inference(pure_predicate_removal,[],[f17])).
% 3.18/0.98  
% 3.18/0.98  fof(f37,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f23])).
% 3.18/0.98  
% 3.18/0.98  fof(f79,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f37])).
% 3.18/0.98  
% 3.18/0.98  fof(f9,axiom,(
% 3.18/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f27,plain,(
% 3.18/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.18/0.98    inference(ennf_transformation,[],[f9])).
% 3.18/0.98  
% 3.18/0.98  fof(f46,plain,(
% 3.18/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.18/0.98    inference(nnf_transformation,[],[f27])).
% 3.18/0.98  
% 3.18/0.98  fof(f65,plain,(
% 3.18/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f46])).
% 3.18/0.98  
% 3.18/0.98  fof(f16,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f36,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f16])).
% 3.18/0.98  
% 3.18/0.98  fof(f78,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f36])).
% 3.18/0.98  
% 3.18/0.98  fof(f6,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f24,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.18/0.98    inference(ennf_transformation,[],[f6])).
% 3.18/0.98  
% 3.18/0.98  fof(f44,plain,(
% 3.18/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.18/0.98    inference(nnf_transformation,[],[f24])).
% 3.18/0.98  
% 3.18/0.98  fof(f45,plain,(
% 3.18/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.18/0.98    inference(flattening,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f58,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f45])).
% 3.18/0.98  
% 3.18/0.98  fof(f97,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 3.18/0.98    inference(definition_unfolding,[],[f58,f90,f91,f91,f53,f90])).
% 3.18/0.98  
% 3.18/0.98  fof(f18,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f38,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f18])).
% 3.18/0.98  
% 3.18/0.98  fof(f80,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f38])).
% 3.18/0.98  
% 3.18/0.98  fof(f85,plain,(
% 3.18/0.98    v1_funct_1(sK4)),
% 3.18/0.98    inference(cnf_transformation,[],[f52])).
% 3.18/0.98  
% 3.18/0.98  fof(f89,plain,(
% 3.18/0.98    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 3.18/0.98    inference(cnf_transformation,[],[f52])).
% 3.18/0.98  
% 3.18/0.98  fof(f110,plain,(
% 3.18/0.98    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),
% 3.18/0.98    inference(definition_unfolding,[],[f89,f91,f91])).
% 3.18/0.98  
% 3.18/0.98  fof(f14,axiom,(
% 3.18/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f33,plain,(
% 3.18/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.18/0.98    inference(ennf_transformation,[],[f14])).
% 3.18/0.98  
% 3.18/0.98  fof(f34,plain,(
% 3.18/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.18/0.98    inference(flattening,[],[f33])).
% 3.18/0.98  
% 3.18/0.98  fof(f76,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f34])).
% 3.18/0.98  
% 3.18/0.98  fof(f105,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f76,f91,f91])).
% 3.18/0.98  
% 3.18/0.98  fof(f11,axiom,(
% 3.18/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f28,plain,(
% 3.18/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(ennf_transformation,[],[f11])).
% 3.18/0.98  
% 3.18/0.98  fof(f29,plain,(
% 3.18/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f28])).
% 3.18/0.98  
% 3.18/0.98  fof(f69,plain,(
% 3.18/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f29])).
% 3.18/0.98  
% 3.18/0.98  fof(f102,plain,(
% 3.18/0.98    ( ! [X0] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f69,f53,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f20,axiom,(
% 3.18/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f40,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.18/0.98    inference(ennf_transformation,[],[f20])).
% 3.18/0.98  
% 3.18/0.98  fof(f41,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.18/0.98    inference(flattening,[],[f40])).
% 3.18/0.98  
% 3.18/0.98  fof(f84,plain,(
% 3.18/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f41])).
% 3.18/0.98  
% 3.18/0.98  fof(f109,plain,(
% 3.18/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f84,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f86,plain,(
% 3.18/0.98    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 3.18/0.98    inference(cnf_transformation,[],[f52])).
% 3.18/0.98  
% 3.18/0.98  fof(f113,plain,(
% 3.18/0.98    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 3.18/0.98    inference(definition_unfolding,[],[f86,f91])).
% 3.18/0.98  
% 3.18/0.98  fof(f88,plain,(
% 3.18/0.98    k1_xboole_0 != sK3),
% 3.18/0.98    inference(cnf_transformation,[],[f52])).
% 3.18/0.98  
% 3.18/0.98  fof(f111,plain,(
% 3.18/0.98    o_0_0_xboole_0 != sK3),
% 3.18/0.98    inference(definition_unfolding,[],[f88,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f15,axiom,(
% 3.18/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f35,plain,(
% 3.18/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.18/0.98    inference(ennf_transformation,[],[f15])).
% 3.18/0.98  
% 3.18/0.98  fof(f77,plain,(
% 3.18/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f35])).
% 3.18/0.98  
% 3.18/0.98  fof(f68,plain,(
% 3.18/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.18/0.98    inference(cnf_transformation,[],[f10])).
% 3.18/0.98  
% 3.18/0.98  fof(f99,plain,(
% 3.18/0.98    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 3.18/0.98    inference(definition_unfolding,[],[f68,f53,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f2,axiom,(
% 3.18/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f54,plain,(
% 3.18/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f2])).
% 3.18/0.98  
% 3.18/0.98  fof(f92,plain,(
% 3.18/0.98    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f54,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f7,axiom,(
% 3.18/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f63,plain,(
% 3.18/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f7])).
% 3.18/0.98  
% 3.18/0.98  fof(f98,plain,(
% 3.18/0.98    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 3.18/0.98    inference(definition_unfolding,[],[f63,f53])).
% 3.18/0.98  
% 3.18/0.98  fof(f12,axiom,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f30,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f12])).
% 3.18/0.98  
% 3.18/0.98  fof(f31,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f30])).
% 3.18/0.98  
% 3.18/0.98  fof(f71,plain,(
% 3.18/0.98    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f31])).
% 3.18/0.98  
% 3.18/0.98  cnf(c_11,plain,
% 3.18/0.98      ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.18/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_26,plain,
% 3.18/0.98      ( r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0 ),
% 3.18/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1500,plain,
% 3.18/0.98      ( o_0_0_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_30,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1499,plain,
% 3.18/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_22,plain,
% 3.18/0.98      ( v4_relat_1(X0,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_9,plain,
% 3.18/0.98      ( ~ v4_relat_1(X0,X1)
% 3.18/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.18/0.98      | ~ v1_relat_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_343,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.18/0.98      | ~ v1_relat_1(X0) ),
% 3.18/0.98      inference(resolution,[status(thm)],[c_22,c_9]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_21,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | v1_relat_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_347,plain,
% 3.18/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_343,c_21]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_348,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_347]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1496,plain,
% 3.18/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.18/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1804,plain,
% 3.18/0.98      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1499,c_1496]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5,plain,
% 3.18/0.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 3.18/0.98      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.18/0.98      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.18/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.18/0.98      | o_0_0_xboole_0 = X0 ),
% 3.18/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1515,plain,
% 3.18/0.98      ( k2_enumset1(X0,X0,X0,X1) = X2
% 3.18/0.98      | k2_enumset1(X1,X1,X1,X1) = X2
% 3.18/0.98      | k2_enumset1(X0,X0,X0,X0) = X2
% 3.18/0.98      | o_0_0_xboole_0 = X2
% 3.18/0.98      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3397,plain,
% 3.18/0.98      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 3.18/0.98      | k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1804,c_1515]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_23,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1503,plain,
% 3.18/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.18/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2502,plain,
% 3.18/0.98      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1499,c_1503]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3509,plain,
% 3.18/0.98      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
% 3.18/0.98      | k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3397,c_2502]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_32,negated_conjecture,
% 3.18/0.98      ( v1_funct_1(sK4) ),
% 3.18/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_28,negated_conjecture,
% 3.18/0.98      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 3.18/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1706,plain,
% 3.18/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 3.18/0.98      | v1_relat_1(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1749,plain,
% 3.18/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 3.18/0.98      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1040,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1743,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
% 3.18/0.99      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 3.18/0.99      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1040]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1849,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 3.18/0.99      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
% 3.18/0.99      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1743]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_19,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.18/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1780,plain,
% 3.18/0.99      ( ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_relat_1(sK4)
% 3.18/0.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK4)
% 3.18/0.99      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3681,plain,
% 3.18/0.99      ( ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_relat_1(sK4)
% 3.18/0.99      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
% 3.18/0.99      | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1780]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3705,plain,
% 3.18/0.99      ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3509,c_32,c_30,c_28,c_1706,c_1749,c_1849,c_3397,
% 3.18/0.99                 c_3681]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_13,plain,
% 3.18/0.99      ( ~ v1_relat_1(X0)
% 3.18/0.99      | k1_relat_1(X0) != o_0_0_xboole_0
% 3.18/0.99      | o_0_0_xboole_0 = X0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1511,plain,
% 3.18/0.99      ( k1_relat_1(X0) != o_0_0_xboole_0
% 3.18/0.99      | o_0_0_xboole_0 = X0
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3711,plain,
% 3.18/0.99      ( sK4 = o_0_0_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_3705,c_1511]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1813,plain,
% 3.18/0.99      ( ~ v1_relat_1(sK4)
% 3.18/0.99      | k1_relat_1(sK4) != o_0_0_xboole_0
% 3.18/0.99      | o_0_0_xboole_0 = sK4 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1039,plain,( X0 = X0 ),theory(equality) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1869,plain,
% 3.18/0.99      ( sK4 = sK4 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1039]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2244,plain,
% 3.18/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1040]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2792,plain,
% 3.18/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2244]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2793,plain,
% 3.18/0.99      ( sK4 != sK4 | sK4 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK4 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2792]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3714,plain,
% 3.18/0.99      ( sK4 = o_0_0_xboole_0 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3711,c_32,c_30,c_28,c_1706,c_1749,c_1813,c_1849,
% 3.18/0.99                 c_1869,c_2793,c_3397,c_3681]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_27,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.18/0.99      | ~ r2_hidden(X3,X1)
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | o_0_0_xboole_0 = X2 ),
% 3.18/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_31,negated_conjecture,
% 3.18/0.99      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_322,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,X1)
% 3.18/0.99      | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
% 3.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.18/0.99      | ~ v1_funct_1(X2)
% 3.18/0.99      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 3.18/0.99      | sK3 != X3
% 3.18/0.99      | sK4 != X2
% 3.18/0.99      | o_0_0_xboole_0 = X3 ),
% 3.18/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_323,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.18/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 3.18/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | o_0_0_xboole_0 = sK3 ),
% 3.18/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_29,negated_conjecture,
% 3.18/0.99      ( o_0_0_xboole_0 != sK3 ),
% 3.18/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_327,plain,
% 3.18/0.99      ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 3.18/0.99      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_323,c_32,c_30,c_29]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_328,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.18/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_327]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1497,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.18/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_20,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1505,plain,
% 3.18/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.18/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2012,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.18/0.99      | r1_tarski(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4),k1_funct_1(sK4,X0)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1497,c_1505]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2598,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.18/0.99      | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,X0)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2502,c_2012]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3721,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.18/0.99      | r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,X0)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_3714,c_2598]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_10,plain,
% 3.18/0.99      ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3743,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.18/0.99      | r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,X0)) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_3721,c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_0,plain,
% 3.18/0.99      ( r1_tarski(o_0_0_xboole_0,X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1520,plain,
% 3.18/0.99      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4020,plain,
% 3.18/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.18/0.99      inference(forward_subsumption_resolution,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3743,c_1520]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4024,plain,
% 3.18/0.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0 ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1500,c_4020]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1506,plain,
% 3.18/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
% 3.18/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 3.18/0.99      | v1_funct_1(X1) != iProver_top
% 3.18/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4402,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2)) = k2_relat_1(X0)
% 3.18/0.99      | k1_relat_1(X0) != o_0_0_xboole_0
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4024,c_1506]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4463,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = k2_relat_1(o_0_0_xboole_0)
% 3.18/0.99      | v1_funct_1(o_0_0_xboole_0) != iProver_top
% 3.18/0.99      | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_11,c_4402]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4495,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = o_0_0_xboole_0
% 3.18/0.99      | v1_funct_1(o_0_0_xboole_0) != iProver_top
% 3.18/0.99      | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_4463,c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2600,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2502,c_28]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3723,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != k2_relat_1(o_0_0_xboole_0) ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_3714,c_2600]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3734,plain,
% 3.18/0.99      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != o_0_0_xboole_0 ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_3723,c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1832,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1835,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1832]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_14,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.18/0.99      | ~ v1_funct_1(X1)
% 3.18/0.99      | v1_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1728,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 3.18/0.99      | v1_funct_1(X0)
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1729,plain,
% 3.18/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) = iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top
% 3.18/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1731,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top
% 3.18/0.99      | v1_funct_1(o_0_0_xboole_0) = iProver_top
% 3.18/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1707,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 3.18/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1706]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1699,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1702,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1698,plain,
% 3.18/0.99      ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/0.99      | v1_relat_1(o_0_0_xboole_0) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1700,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/0.99      | v1_relat_1(o_0_0_xboole_0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1698]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_35,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_33,plain,
% 3.18/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4509,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
% 3.18/0.99      inference(grounding,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1702:[bind(X1,$fot(o_0_0_xboole_0)),
% 3.18/0.99                 bind(X0,$fot(o_0_0_xboole_0))]]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4510,plain,
% 3.18/0.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) != iProver_top
% 3.18/0.99      | v1_relat_1(o_0_0_xboole_0) = iProver_top ),
% 3.18/0.99      inference(grounding,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1700:[bind(X1,$fot(o_0_0_xboole_0)),
% 3.18/0.99                 bind(X0,$fot(o_0_0_xboole_0))]]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(contradiction,plain,
% 3.18/0.99      ( $false ),
% 3.18/0.99      inference(minisat,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4495,c_3734,c_1835,c_1731,c_1707,c_4509,c_4510,c_35,
% 3.18/0.99                 c_33]) ).
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  ------                               Statistics
% 3.18/0.99  
% 3.18/0.99  ------ General
% 3.18/0.99  
% 3.18/0.99  abstr_ref_over_cycles:                  0
% 3.18/0.99  abstr_ref_under_cycles:                 0
% 3.18/0.99  gc_basic_clause_elim:                   0
% 3.18/0.99  forced_gc_time:                         0
% 3.18/0.99  parsing_time:                           0.009
% 3.18/0.99  unif_index_cands_time:                  0.
% 3.18/0.99  unif_index_add_time:                    0.
% 3.18/0.99  orderings_time:                         0.
% 3.18/0.99  out_proof_time:                         0.01
% 3.18/0.99  total_time:                             0.159
% 3.18/0.99  num_of_symbols:                         52
% 3.18/0.99  num_of_terms:                           3095
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing
% 3.18/0.99  
% 3.18/0.99  num_of_splits:                          0
% 3.18/0.99  num_of_split_atoms:                     0
% 3.18/0.99  num_of_reused_defs:                     0
% 3.18/0.99  num_eq_ax_congr_red:                    20
% 3.18/0.99  num_of_sem_filtered_clauses:            1
% 3.18/0.99  num_of_subtypes:                        0
% 3.18/0.99  monotx_restored_types:                  0
% 3.18/0.99  sat_num_of_epr_types:                   0
% 3.18/0.99  sat_num_of_non_cyclic_types:            0
% 3.18/0.99  sat_guarded_non_collapsed_types:        0
% 3.18/0.99  num_pure_diseq_elim:                    0
% 3.18/0.99  simp_replaced_by:                       0
% 3.18/0.99  res_preprocessed:                       152
% 3.18/0.99  prep_upred:                             0
% 3.18/0.99  prep_unflattend:                        53
% 3.18/0.99  smt_new_axioms:                         0
% 3.18/0.99  pred_elim_cands:                        5
% 3.18/0.99  pred_elim:                              2
% 3.18/0.99  pred_elim_cl:                           3
% 3.18/0.99  pred_elim_cycles:                       6
% 3.18/0.99  merged_defs:                            0
% 3.18/0.99  merged_defs_ncl:                        0
% 3.18/0.99  bin_hyper_res:                          0
% 3.18/0.99  prep_cycles:                            4
% 3.18/0.99  pred_elim_time:                         0.009
% 3.18/0.99  splitting_time:                         0.
% 3.18/0.99  sem_filter_time:                        0.
% 3.18/0.99  monotx_time:                            0.
% 3.18/0.99  subtype_inf_time:                       0.
% 3.18/0.99  
% 3.18/0.99  ------ Problem properties
% 3.18/0.99  
% 3.18/0.99  clauses:                                30
% 3.18/0.99  conjectures:                            4
% 3.18/0.99  epr:                                    4
% 3.18/0.99  horn:                                   28
% 3.18/0.99  ground:                                 6
% 3.18/0.99  unary:                                  15
% 3.18/0.99  binary:                                 7
% 3.18/0.99  lits:                                   57
% 3.18/0.99  lits_eq:                                22
% 3.18/0.99  fd_pure:                                0
% 3.18/0.99  fd_pseudo:                              0
% 3.18/0.99  fd_cond:                                5
% 3.18/0.99  fd_pseudo_cond:                         1
% 3.18/0.99  ac_symbols:                             0
% 3.18/0.99  
% 3.18/0.99  ------ Propositional Solver
% 3.18/0.99  
% 3.18/0.99  prop_solver_calls:                      28
% 3.18/0.99  prop_fast_solver_calls:                 907
% 3.18/0.99  smt_solver_calls:                       0
% 3.18/0.99  smt_fast_solver_calls:                  0
% 3.18/0.99  prop_num_of_clauses:                    1311
% 3.18/0.99  prop_preprocess_simplified:             5546
% 3.18/0.99  prop_fo_subsumed:                       18
% 3.18/0.99  prop_solver_time:                       0.
% 3.18/0.99  smt_solver_time:                        0.
% 3.18/0.99  smt_fast_solver_time:                   0.
% 3.18/0.99  prop_fast_solver_time:                  0.
% 3.18/0.99  prop_unsat_core_time:                   0.
% 3.18/0.99  
% 3.18/0.99  ------ QBF
% 3.18/0.99  
% 3.18/0.99  qbf_q_res:                              0
% 3.18/0.99  qbf_num_tautologies:                    0
% 3.18/0.99  qbf_prep_cycles:                        0
% 3.18/0.99  
% 3.18/0.99  ------ BMC1
% 3.18/0.99  
% 3.18/0.99  bmc1_current_bound:                     -1
% 3.18/0.99  bmc1_last_solved_bound:                 -1
% 3.18/0.99  bmc1_unsat_core_size:                   -1
% 3.18/0.99  bmc1_unsat_core_parents_size:           -1
% 3.18/0.99  bmc1_merge_next_fun:                    0
% 3.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation
% 3.18/0.99  
% 3.18/0.99  inst_num_of_clauses:                    467
% 3.18/0.99  inst_num_in_passive:                    104
% 3.18/0.99  inst_num_in_active:                     276
% 3.18/0.99  inst_num_in_unprocessed:                87
% 3.18/0.99  inst_num_of_loops:                      350
% 3.18/0.99  inst_num_of_learning_restarts:          0
% 3.18/0.99  inst_num_moves_active_passive:          71
% 3.18/0.99  inst_lit_activity:                      0
% 3.18/0.99  inst_lit_activity_moves:                0
% 3.18/0.99  inst_num_tautologies:                   0
% 3.18/0.99  inst_num_prop_implied:                  0
% 3.18/0.99  inst_num_existing_simplified:           0
% 3.18/0.99  inst_num_eq_res_simplified:             0
% 3.18/0.99  inst_num_child_elim:                    0
% 3.18/0.99  inst_num_of_dismatching_blockings:      60
% 3.18/0.99  inst_num_of_non_proper_insts:           325
% 3.18/0.99  inst_num_of_duplicates:                 0
% 3.18/0.99  inst_inst_num_from_inst_to_res:         0
% 3.18/0.99  inst_dismatching_checking_time:         0.
% 3.18/0.99  
% 3.18/0.99  ------ Resolution
% 3.18/0.99  
% 3.18/0.99  res_num_of_clauses:                     0
% 3.18/0.99  res_num_in_passive:                     0
% 3.18/0.99  res_num_in_active:                      0
% 3.18/0.99  res_num_of_loops:                       156
% 3.18/0.99  res_forward_subset_subsumed:            46
% 3.18/0.99  res_backward_subset_subsumed:           0
% 3.18/0.99  res_forward_subsumed:                   2
% 3.18/0.99  res_backward_subsumed:                  0
% 3.18/0.99  res_forward_subsumption_resolution:     1
% 3.18/0.99  res_backward_subsumption_resolution:    0
% 3.18/0.99  res_clause_to_clause_subsumption:       187
% 3.18/0.99  res_orphan_elimination:                 0
% 3.18/0.99  res_tautology_del:                      81
% 3.18/0.99  res_num_eq_res_simplified:              0
% 3.18/0.99  res_num_sel_changes:                    0
% 3.18/0.99  res_moves_from_active_to_pass:          0
% 3.18/0.99  
% 3.18/0.99  ------ Superposition
% 3.18/0.99  
% 3.18/0.99  sup_time_total:                         0.
% 3.18/0.99  sup_time_generating:                    0.
% 3.18/0.99  sup_time_sim_full:                      0.
% 3.18/0.99  sup_time_sim_immed:                     0.
% 3.18/0.99  
% 3.18/0.99  sup_num_of_clauses:                     67
% 3.18/0.99  sup_num_in_active:                      48
% 3.18/0.99  sup_num_in_passive:                     19
% 3.18/0.99  sup_num_of_loops:                       68
% 3.18/0.99  sup_fw_superposition:                   103
% 3.18/0.99  sup_bw_superposition:                   56
% 3.18/0.99  sup_immediate_simplified:               38
% 3.18/0.99  sup_given_eliminated:                   1
% 3.18/0.99  comparisons_done:                       0
% 3.18/0.99  comparisons_avoided:                    12
% 3.18/0.99  
% 3.18/0.99  ------ Simplifications
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  sim_fw_subset_subsumed:                 7
% 3.18/0.99  sim_bw_subset_subsumed:                 15
% 3.18/0.99  sim_fw_subsumed:                        21
% 3.18/0.99  sim_bw_subsumed:                        1
% 3.18/0.99  sim_fw_subsumption_res:                 2
% 3.18/0.99  sim_bw_subsumption_res:                 0
% 3.18/0.99  sim_tautology_del:                      0
% 3.18/0.99  sim_eq_tautology_del:                   9
% 3.18/0.99  sim_eq_res_simp:                        0
% 3.18/0.99  sim_fw_demodulated:                     1
% 3.18/0.99  sim_bw_demodulated:                     17
% 3.18/0.99  sim_light_normalised:                   10
% 3.18/0.99  sim_joinable_taut:                      0
% 3.18/0.99  sim_joinable_simp:                      0
% 3.18/0.99  sim_ac_normalised:                      0
% 3.18/0.99  sim_smt_subsumption:                    0
% 3.18/0.99  
%------------------------------------------------------------------------------
