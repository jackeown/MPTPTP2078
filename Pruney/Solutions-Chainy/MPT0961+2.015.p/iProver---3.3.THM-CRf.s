%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:57 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 384 expanded)
%              Number of clauses        :   71 ( 142 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  345 (1480 expanded)
%              Number of equality atoms :  174 ( 427 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
        | ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
        | ~ v1_funct_1(sK4) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
      | ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
      | ~ v1_funct_1(sK4) )
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f47])).

fof(f84,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_932,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3332,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != X0
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_4364,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_relat_1(sK4)
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3332])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2006,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2759,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1806,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2656,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_931,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2151,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_2389,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_2369,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1811,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_2150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_2315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_2317,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2005,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2279,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_1550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_182,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_34])).

cnf(c_183,negated_conjecture,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK4) != X2
    | k1_relat_1(sK4) != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_183])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | k1_relset_1(k1_relat_1(sK4),k2_relat_1(sK4),sK4) != k1_relat_1(sK4)
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_689,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_681,c_26])).

cnf(c_1533,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2164,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1533])).

cnf(c_35,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1749,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1750,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_2171,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2164,c_36,c_1750])).

cnf(c_1544,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2241,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2171,c_1544])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2250,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2241,c_7])).

cnf(c_2059,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2060,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2059])).

cnf(c_1844,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1847,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1844])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1827,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | sK4 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1828,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_27,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_637,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK4) != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_183])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))
    | k2_relat_1(sK4) != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_1535,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1672,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK4) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1535,c_7])).

cnf(c_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK4) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1672])).

cnf(c_1741,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1781,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK4) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1672,c_35,c_98,c_103,c_1697,c_1741,c_1749])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK4) != X1
    | k1_relat_1(sK4) != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_183])).

cnf(c_665,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_1534,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1663,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1534,c_8])).

cnf(c_1742,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_1773,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1663,c_36,c_1742,c_1750])).

cnf(c_1774,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1773])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4365,c_4364,c_2759,c_2656,c_2389,c_2369,c_2317,c_2279,c_2250,c_2164,c_2060,c_1847,c_1828,c_1781,c_1774,c_1750,c_1749,c_1741,c_638,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.99  
% 2.33/0.99  ------  iProver source info
% 2.33/0.99  
% 2.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.99  git: non_committed_changes: false
% 2.33/0.99  git: last_make_outside_of_git: false
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     num_symb
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       true
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  ------ Parsing...
% 2.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 29
% 2.33/0.99  conjectures                             1
% 2.33/0.99  EPR                                     8
% 2.33/0.99  Horn                                    26
% 2.33/0.99  unary                                   9
% 2.33/0.99  binary                                  10
% 2.33/0.99  lits                                    62
% 2.33/0.99  lits eq                                 19
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 3
% 2.33/0.99  fd_pseudo_cond                          3
% 2.33/0.99  AC symbols                              0
% 2.33/0.99  
% 2.33/0.99  ------ Schedule dynamic 5 is on 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  Current options:
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     none
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       false
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ Proving...
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  % SZS status Theorem for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  fof(f16,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f28,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(ennf_transformation,[],[f16])).
% 2.33/0.99  
% 2.33/0.99  fof(f75,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f28])).
% 2.33/0.99  
% 2.33/0.99  fof(f5,axiom,(
% 2.33/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f55,plain,(
% 2.33/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f5])).
% 2.33/0.99  
% 2.33/0.99  fof(f7,axiom,(
% 2.33/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f39,plain,(
% 2.33/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.33/0.99    inference(nnf_transformation,[],[f7])).
% 2.33/0.99  
% 2.33/0.99  fof(f60,plain,(
% 2.33/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f39])).
% 2.33/0.99  
% 2.33/0.99  fof(f17,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f29,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(ennf_transformation,[],[f17])).
% 2.33/0.99  
% 2.33/0.99  fof(f30,plain,(
% 2.33/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(flattening,[],[f29])).
% 2.33/0.99  
% 2.33/0.99  fof(f46,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(nnf_transformation,[],[f30])).
% 2.33/0.99  
% 2.33/0.99  fof(f78,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f18,conjecture,(
% 2.33/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f19,negated_conjecture,(
% 2.33/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.33/0.99    inference(negated_conjecture,[],[f18])).
% 2.33/0.99  
% 2.33/0.99  fof(f31,plain,(
% 2.33/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f19])).
% 2.33/0.99  
% 2.33/0.99  fof(f32,plain,(
% 2.33/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.33/0.99    inference(flattening,[],[f31])).
% 2.33/0.99  
% 2.33/0.99  fof(f47,plain,(
% 2.33/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) | ~v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4)) | ~v1_funct_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f48,plain,(
% 2.33/0.99    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) | ~v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4)) | ~v1_funct_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f47])).
% 2.33/0.99  
% 2.33/0.99  fof(f84,plain,(
% 2.33/0.99    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) | ~v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4)) | ~v1_funct_1(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f48])).
% 2.33/0.99  
% 2.33/0.99  fof(f83,plain,(
% 2.33/0.99    v1_funct_1(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f48])).
% 2.33/0.99  
% 2.33/0.99  fof(f82,plain,(
% 2.33/0.99    v1_relat_1(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f48])).
% 2.33/0.99  
% 2.33/0.99  fof(f10,axiom,(
% 2.33/0.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f23,plain,(
% 2.33/0.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.33/0.99    inference(ennf_transformation,[],[f10])).
% 2.33/0.99  
% 2.33/0.99  fof(f66,plain,(
% 2.33/0.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f23])).
% 2.33/0.99  
% 2.33/0.99  fof(f6,axiom,(
% 2.33/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f37,plain,(
% 2.33/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.99    inference(nnf_transformation,[],[f6])).
% 2.33/0.99  
% 2.33/0.99  fof(f38,plain,(
% 2.33/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.99    inference(flattening,[],[f37])).
% 2.33/0.99  
% 2.33/0.99  fof(f58,plain,(
% 2.33/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.33/0.99    inference(cnf_transformation,[],[f38])).
% 2.33/0.99  
% 2.33/0.99  fof(f87,plain,(
% 2.33/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.33/0.99    inference(equality_resolution,[],[f58])).
% 2.33/0.99  
% 2.33/0.99  fof(f4,axiom,(
% 2.33/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f35,plain,(
% 2.33/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.99    inference(nnf_transformation,[],[f4])).
% 2.33/0.99  
% 2.33/0.99  fof(f36,plain,(
% 2.33/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.99    inference(flattening,[],[f35])).
% 2.33/0.99  
% 2.33/0.99  fof(f54,plain,(
% 2.33/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f36])).
% 2.33/0.99  
% 2.33/0.99  fof(f81,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f91,plain,(
% 2.33/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(equality_resolution,[],[f81])).
% 2.33/0.99  
% 2.33/0.99  fof(f92,plain,(
% 2.33/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.33/0.99    inference(equality_resolution,[],[f91])).
% 2.33/0.99  
% 2.33/0.99  fof(f79,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f94,plain,(
% 2.33/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.33/0.99    inference(equality_resolution,[],[f79])).
% 2.33/0.99  
% 2.33/0.99  fof(f57,plain,(
% 2.33/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.33/0.99    inference(cnf_transformation,[],[f38])).
% 2.33/0.99  
% 2.33/0.99  fof(f88,plain,(
% 2.33/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.33/0.99    inference(equality_resolution,[],[f57])).
% 2.33/0.99  
% 2.33/0.99  cnf(c_26,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4365,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_932,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3332,plain,
% 2.33/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != X0
% 2.33/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_xboole_0
% 2.33/0.99      | k1_xboole_0 != X0 ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_932]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4364,plain,
% 2.33/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_relat_1(sK4)
% 2.33/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) = k1_xboole_0
% 2.33/0.99      | k1_xboole_0 != k1_relat_1(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_3332]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_6,plain,
% 2.33/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2006,plain,
% 2.33/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2759,plain,
% 2.33/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2006]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_10,plain,
% 2.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1806,plain,
% 2.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2654,plain,
% 2.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1806]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2656,plain,
% 2.33/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2654]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_931,plain,( X0 = X0 ),theory(equality) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2151,plain,
% 2.33/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_931]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2389,plain,
% 2.33/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2151]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2369,plain,
% 2.33/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2006]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_938,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.33/0.99      theory(equality) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1811,plain,
% 2.33/0.99      ( m1_subset_1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.33/0.99      | X0 != X2
% 2.33/0.99      | X1 != k1_zfmisc_1(X3) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_938]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2150,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.33/0.99      | X2 != X0
% 2.33/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1811]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2315,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
% 2.33/0.99      | sK4 != X0 ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2150]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2317,plain,
% 2.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
% 2.33/0.99      | sK4 != k1_xboole_0 ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2315]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2005,plain,
% 2.33/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1806]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2279,plain,
% 2.33/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))
% 2.33/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2005]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1550,plain,
% 2.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.33/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_30,plain,
% 2.33/0.99      ( v1_funct_2(X0,X1,X2)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.99      | k1_xboole_0 = X2 ),
% 2.33/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_33,negated_conjecture,
% 2.33/0.99      ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
% 2.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/0.99      | ~ v1_funct_1(sK4) ),
% 2.33/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_34,negated_conjecture,
% 2.33/0.99      ( v1_funct_1(sK4) ),
% 2.33/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_182,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/0.99      | ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4)) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_33,c_34]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_183,negated_conjecture,
% 2.33/0.99      ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
% 2.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_182]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_680,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.99      | k2_relat_1(sK4) != X2
% 2.33/0.99      | k1_relat_1(sK4) != X1
% 2.33/0.99      | sK4 != X0
% 2.33/0.99      | k1_xboole_0 = X2 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_183]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_681,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/0.99      | k1_relset_1(k1_relat_1(sK4),k2_relat_1(sK4),sK4) != k1_relat_1(sK4)
% 2.33/0.99      | k1_xboole_0 = k2_relat_1(sK4) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_680]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_689,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | k1_xboole_0 = k2_relat_1(sK4) ),
% 2.33/1.00      inference(forward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_681,c_26]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1533,plain,
% 2.33/1.00      ( k1_xboole_0 = k2_relat_1(sK4)
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2164,plain,
% 2.33/1.00      ( k2_relat_1(sK4) = k1_xboole_0
% 2.33/1.00      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1550,c_1533]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_35,negated_conjecture,
% 2.33/1.00      ( v1_relat_1(sK4) ),
% 2.33/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_36,plain,
% 2.33/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_17,plain,
% 2.33/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.33/1.00      | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1749,plain,
% 2.33/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))
% 2.33/1.00      | ~ v1_relat_1(sK4) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1750,plain,
% 2.33/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top
% 2.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2171,plain,
% 2.33/1.00      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2164,c_36,c_1750]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1544,plain,
% 2.33/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2241,plain,
% 2.33/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) = iProver_top
% 2.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2171,c_1544]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7,plain,
% 2.33/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2250,plain,
% 2.33/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top
% 2.33/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2241,c_7]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2059,plain,
% 2.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 2.33/1.00      | ~ r1_tarski(sK4,k1_xboole_0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2060,plain,
% 2.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.33/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2059]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1844,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,sK4) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1847,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1844]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1827,plain,
% 2.33/1.00      ( ~ r1_tarski(sK4,k1_xboole_0)
% 2.33/1.00      | ~ r1_tarski(k1_xboole_0,sK4)
% 2.33/1.00      | sK4 = k1_xboole_0 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1828,plain,
% 2.33/1.00      ( sK4 = k1_xboole_0
% 2.33/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.33/1.00      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1827]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_27,plain,
% 2.33/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.33/1.00      | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_637,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.33/1.00      | k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) != X0
% 2.33/1.00      | sK4 != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_183]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_638,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))
% 2.33/1.00      | k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | sK4 != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = k1_relat_1(sK4) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_637]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1535,plain,
% 2.33/1.00      ( k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | sK4 != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = k1_relat_1(sK4)
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
% 2.33/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1672,plain,
% 2.33/1.00      ( k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 2.33/1.00      | sK4 != k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
% 2.33/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_1535,c_7]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_98,plain,
% 2.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.33/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_103,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1697,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.33/1.00      | k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 2.33/1.00      | sK4 != k1_xboole_0 ),
% 2.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1672]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1741,plain,
% 2.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | ~ r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1781,plain,
% 2.33/1.00      ( k2_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 2.33/1.00      | sK4 != k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1672,c_35,c_98,c_103,c_1697,c_1741,c_1749]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_29,plain,
% 2.33/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_664,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.33/1.00      | k2_relat_1(sK4) != X1
% 2.33/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | sK4 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_183]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_665,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))
% 2.33/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
% 2.33/1.00      | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) != k1_xboole_0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_664]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1534,plain,
% 2.33/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_8,plain,
% 2.33/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1663,plain,
% 2.33/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_1534,c_8]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1742,plain,
% 2.33/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top
% 2.33/1.00      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1773,plain,
% 2.33/1.00      ( k1_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1663,c_36,c_1742,c_1750]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1774,plain,
% 2.33/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK4),sK4) != k1_xboole_0
% 2.33/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_1773]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_4365,c_4364,c_2759,c_2656,c_2389,c_2369,c_2317,c_2279,
% 2.33/1.00                 c_2250,c_2164,c_2060,c_1847,c_1828,c_1781,c_1774,c_1750,
% 2.33/1.00                 c_1749,c_1741,c_638,c_36,c_35]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.01
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.008
% 2.33/1.00  total_time:                             0.119
% 2.33/1.00  num_of_symbols:                         51
% 2.33/1.00  num_of_terms:                           3103
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    26
% 2.33/1.00  num_of_sem_filtered_clauses:            3
% 2.33/1.00  num_of_subtypes:                        0
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        0
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       149
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        35
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        5
% 2.33/1.00  pred_elim:                              1
% 2.33/1.00  pred_elim_cl:                           4
% 2.33/1.00  pred_elim_cycles:                       4
% 2.33/1.00  merged_defs:                            8
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          9
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.007
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.001
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                29
% 2.33/1.00  conjectures:                            1
% 2.33/1.00  epr:                                    8
% 2.33/1.00  horn:                                   26
% 2.33/1.00  ground:                                 5
% 2.33/1.00  unary:                                  9
% 2.33/1.00  binary:                                 10
% 2.33/1.00  lits:                                   62
% 2.33/1.00  lits_eq:                                19
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                3
% 2.33/1.00  fd_pseudo_cond:                         3
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      30
% 2.33/1.00  prop_fast_solver_calls:                 892
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1329
% 2.33/1.00  prop_preprocess_simplified:             5164
% 2.33/1.00  prop_fo_subsumed:                       17
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    379
% 2.33/1.00  inst_num_in_passive:                    117
% 2.33/1.00  inst_num_in_active:                     257
% 2.33/1.00  inst_num_in_unprocessed:                4
% 2.33/1.00  inst_num_of_loops:                      313
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          49
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      164
% 2.33/1.00  inst_num_of_non_proper_insts:           352
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       153
% 2.33/1.00  res_forward_subset_subsumed:            22
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  0
% 2.33/1.00  res_forward_subsumption_resolution:     2
% 2.33/1.00  res_backward_subsumption_resolution:    0
% 2.33/1.00  res_clause_to_clause_subsumption:       371
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      32
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     82
% 2.33/1.00  sup_num_in_active:                      45
% 2.33/1.00  sup_num_in_passive:                     37
% 2.33/1.00  sup_num_of_loops:                       62
% 2.33/1.00  sup_fw_superposition:                   73
% 2.33/1.00  sup_bw_superposition:                   33
% 2.33/1.00  sup_immediate_simplified:               35
% 2.33/1.00  sup_given_eliminated:                   1
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 6
% 2.33/1.00  sim_bw_subset_subsumed:                 1
% 2.33/1.00  sim_fw_subsumed:                        16
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 3
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      5
% 2.33/1.00  sim_eq_tautology_del:                   4
% 2.33/1.00  sim_eq_res_simp:                        1
% 2.33/1.00  sim_fw_demodulated:                     7
% 2.33/1.00  sim_bw_demodulated:                     18
% 2.33/1.00  sim_light_normalised:                   13
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
