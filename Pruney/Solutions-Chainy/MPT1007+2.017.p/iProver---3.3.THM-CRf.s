%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:45 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 ( 382 expanded)
%              Number of equality atoms :   58 ( 113 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f107,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f106])).

fof(f108,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f107])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f108])).

fof(f23,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK3(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK3(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f58])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
      & k1_xboole_0 != sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
      & v1_funct_2(sK6,k1_tarski(sK4),sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    & k1_xboole_0 != sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
    & v1_funct_2(sK6,k1_tarski(sK4),sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f60])).

fof(f102,plain,(
    v1_funct_2(sK6,k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f112,plain,(
    v1_funct_2(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f102,f108])).

fof(f101,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) ),
    inference(cnf_transformation,[],[f61])).

fof(f111,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5))) ),
    inference(definition_unfolding,[],[f103,f108])).

fof(f104,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    ~ r2_hidden(k1_funct_1(sK6,sK4),sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(definition_unfolding,[],[f82,f106])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1915,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_33,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1910,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1922,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3946,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_1922])).

cnf(c_6152,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_3946])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1
    | sK5 != X2
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_464,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)))
    | ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(k1_funct_1(sK6,X0),sK5)
    | ~ v1_funct_1(sK6)
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_468,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(k1_funct_1(sK6,X0),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_39,c_37,c_36])).

cnf(c_1908,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_18829,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6152,c_1908])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1909,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19223,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18829,c_1909])).

cnf(c_19412,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_19223])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_501,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_19443,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19412,c_501])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.95/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.95/1.49  
% 6.95/1.49  ------  iProver source info
% 6.95/1.49  
% 6.95/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.95/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.95/1.49  git: non_committed_changes: false
% 6.95/1.49  git: last_make_outside_of_git: false
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  
% 6.95/1.49  ------ Input Options
% 6.95/1.49  
% 6.95/1.49  --out_options                           all
% 6.95/1.49  --tptp_safe_out                         true
% 6.95/1.49  --problem_path                          ""
% 6.95/1.49  --include_path                          ""
% 6.95/1.49  --clausifier                            res/vclausify_rel
% 6.95/1.49  --clausifier_options                    --mode clausify
% 6.95/1.49  --stdin                                 false
% 6.95/1.49  --stats_out                             all
% 6.95/1.49  
% 6.95/1.49  ------ General Options
% 6.95/1.49  
% 6.95/1.49  --fof                                   false
% 6.95/1.49  --time_out_real                         305.
% 6.95/1.49  --time_out_virtual                      -1.
% 6.95/1.49  --symbol_type_check                     false
% 6.95/1.49  --clausify_out                          false
% 6.95/1.49  --sig_cnt_out                           false
% 6.95/1.49  --trig_cnt_out                          false
% 6.95/1.49  --trig_cnt_out_tolerance                1.
% 6.95/1.49  --trig_cnt_out_sk_spl                   false
% 6.95/1.49  --abstr_cl_out                          false
% 6.95/1.49  
% 6.95/1.49  ------ Global Options
% 6.95/1.49  
% 6.95/1.49  --schedule                              default
% 6.95/1.49  --add_important_lit                     false
% 6.95/1.49  --prop_solver_per_cl                    1000
% 6.95/1.49  --min_unsat_core                        false
% 6.95/1.49  --soft_assumptions                      false
% 6.95/1.49  --soft_lemma_size                       3
% 6.95/1.49  --prop_impl_unit_size                   0
% 6.95/1.49  --prop_impl_unit                        []
% 6.95/1.49  --share_sel_clauses                     true
% 6.95/1.49  --reset_solvers                         false
% 6.95/1.49  --bc_imp_inh                            [conj_cone]
% 6.95/1.49  --conj_cone_tolerance                   3.
% 6.95/1.49  --extra_neg_conj                        none
% 6.95/1.49  --large_theory_mode                     true
% 6.95/1.49  --prolific_symb_bound                   200
% 6.95/1.49  --lt_threshold                          2000
% 6.95/1.49  --clause_weak_htbl                      true
% 6.95/1.49  --gc_record_bc_elim                     false
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing Options
% 6.95/1.49  
% 6.95/1.49  --preprocessing_flag                    true
% 6.95/1.49  --time_out_prep_mult                    0.1
% 6.95/1.49  --splitting_mode                        input
% 6.95/1.49  --splitting_grd                         true
% 6.95/1.49  --splitting_cvd                         false
% 6.95/1.49  --splitting_cvd_svl                     false
% 6.95/1.49  --splitting_nvd                         32
% 6.95/1.49  --sub_typing                            true
% 6.95/1.49  --prep_gs_sim                           true
% 6.95/1.49  --prep_unflatten                        true
% 6.95/1.49  --prep_res_sim                          true
% 6.95/1.49  --prep_upred                            true
% 6.95/1.49  --prep_sem_filter                       exhaustive
% 6.95/1.49  --prep_sem_filter_out                   false
% 6.95/1.49  --pred_elim                             true
% 6.95/1.49  --res_sim_input                         true
% 6.95/1.49  --eq_ax_congr_red                       true
% 6.95/1.49  --pure_diseq_elim                       true
% 6.95/1.49  --brand_transform                       false
% 6.95/1.49  --non_eq_to_eq                          false
% 6.95/1.49  --prep_def_merge                        true
% 6.95/1.49  --prep_def_merge_prop_impl              false
% 6.95/1.49  --prep_def_merge_mbd                    true
% 6.95/1.49  --prep_def_merge_tr_red                 false
% 6.95/1.49  --prep_def_merge_tr_cl                  false
% 6.95/1.49  --smt_preprocessing                     true
% 6.95/1.49  --smt_ac_axioms                         fast
% 6.95/1.49  --preprocessed_out                      false
% 6.95/1.49  --preprocessed_stats                    false
% 6.95/1.49  
% 6.95/1.49  ------ Abstraction refinement Options
% 6.95/1.49  
% 6.95/1.49  --abstr_ref                             []
% 6.95/1.49  --abstr_ref_prep                        false
% 6.95/1.49  --abstr_ref_until_sat                   false
% 6.95/1.49  --abstr_ref_sig_restrict                funpre
% 6.95/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.95/1.49  --abstr_ref_under                       []
% 6.95/1.49  
% 6.95/1.49  ------ SAT Options
% 6.95/1.49  
% 6.95/1.49  --sat_mode                              false
% 6.95/1.49  --sat_fm_restart_options                ""
% 6.95/1.49  --sat_gr_def                            false
% 6.95/1.49  --sat_epr_types                         true
% 6.95/1.49  --sat_non_cyclic_types                  false
% 6.95/1.49  --sat_finite_models                     false
% 6.95/1.49  --sat_fm_lemmas                         false
% 6.95/1.49  --sat_fm_prep                           false
% 6.95/1.49  --sat_fm_uc_incr                        true
% 6.95/1.49  --sat_out_model                         small
% 6.95/1.49  --sat_out_clauses                       false
% 6.95/1.49  
% 6.95/1.49  ------ QBF Options
% 6.95/1.49  
% 6.95/1.49  --qbf_mode                              false
% 6.95/1.49  --qbf_elim_univ                         false
% 6.95/1.49  --qbf_dom_inst                          none
% 6.95/1.49  --qbf_dom_pre_inst                      false
% 6.95/1.49  --qbf_sk_in                             false
% 6.95/1.49  --qbf_pred_elim                         true
% 6.95/1.49  --qbf_split                             512
% 6.95/1.49  
% 6.95/1.49  ------ BMC1 Options
% 6.95/1.49  
% 6.95/1.49  --bmc1_incremental                      false
% 6.95/1.49  --bmc1_axioms                           reachable_all
% 6.95/1.49  --bmc1_min_bound                        0
% 6.95/1.49  --bmc1_max_bound                        -1
% 6.95/1.49  --bmc1_max_bound_default                -1
% 6.95/1.49  --bmc1_symbol_reachability              true
% 6.95/1.49  --bmc1_property_lemmas                  false
% 6.95/1.49  --bmc1_k_induction                      false
% 6.95/1.49  --bmc1_non_equiv_states                 false
% 6.95/1.49  --bmc1_deadlock                         false
% 6.95/1.49  --bmc1_ucm                              false
% 6.95/1.49  --bmc1_add_unsat_core                   none
% 6.95/1.49  --bmc1_unsat_core_children              false
% 6.95/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.95/1.49  --bmc1_out_stat                         full
% 6.95/1.49  --bmc1_ground_init                      false
% 6.95/1.49  --bmc1_pre_inst_next_state              false
% 6.95/1.49  --bmc1_pre_inst_state                   false
% 6.95/1.49  --bmc1_pre_inst_reach_state             false
% 6.95/1.49  --bmc1_out_unsat_core                   false
% 6.95/1.49  --bmc1_aig_witness_out                  false
% 6.95/1.49  --bmc1_verbose                          false
% 6.95/1.49  --bmc1_dump_clauses_tptp                false
% 6.95/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.95/1.49  --bmc1_dump_file                        -
% 6.95/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.95/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.95/1.49  --bmc1_ucm_extend_mode                  1
% 6.95/1.49  --bmc1_ucm_init_mode                    2
% 6.95/1.49  --bmc1_ucm_cone_mode                    none
% 6.95/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.95/1.49  --bmc1_ucm_relax_model                  4
% 6.95/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.95/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.95/1.49  --bmc1_ucm_layered_model                none
% 6.95/1.49  --bmc1_ucm_max_lemma_size               10
% 6.95/1.49  
% 6.95/1.49  ------ AIG Options
% 6.95/1.49  
% 6.95/1.49  --aig_mode                              false
% 6.95/1.49  
% 6.95/1.49  ------ Instantiation Options
% 6.95/1.49  
% 6.95/1.49  --instantiation_flag                    true
% 6.95/1.49  --inst_sos_flag                         false
% 6.95/1.49  --inst_sos_phase                        true
% 6.95/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.95/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.95/1.49  --inst_lit_sel_side                     num_symb
% 6.95/1.49  --inst_solver_per_active                1400
% 6.95/1.49  --inst_solver_calls_frac                1.
% 6.95/1.49  --inst_passive_queue_type               priority_queues
% 6.95/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.95/1.49  --inst_passive_queues_freq              [25;2]
% 6.95/1.49  --inst_dismatching                      true
% 6.95/1.49  --inst_eager_unprocessed_to_passive     true
% 6.95/1.49  --inst_prop_sim_given                   true
% 6.95/1.49  --inst_prop_sim_new                     false
% 6.95/1.49  --inst_subs_new                         false
% 6.95/1.49  --inst_eq_res_simp                      false
% 6.95/1.49  --inst_subs_given                       false
% 6.95/1.49  --inst_orphan_elimination               true
% 6.95/1.49  --inst_learning_loop_flag               true
% 6.95/1.49  --inst_learning_start                   3000
% 6.95/1.49  --inst_learning_factor                  2
% 6.95/1.49  --inst_start_prop_sim_after_learn       3
% 6.95/1.49  --inst_sel_renew                        solver
% 6.95/1.49  --inst_lit_activity_flag                true
% 6.95/1.49  --inst_restr_to_given                   false
% 6.95/1.49  --inst_activity_threshold               500
% 6.95/1.49  --inst_out_proof                        true
% 6.95/1.49  
% 6.95/1.49  ------ Resolution Options
% 6.95/1.49  
% 6.95/1.49  --resolution_flag                       true
% 6.95/1.49  --res_lit_sel                           adaptive
% 6.95/1.49  --res_lit_sel_side                      none
% 6.95/1.49  --res_ordering                          kbo
% 6.95/1.49  --res_to_prop_solver                    active
% 6.95/1.49  --res_prop_simpl_new                    false
% 6.95/1.49  --res_prop_simpl_given                  true
% 6.95/1.49  --res_passive_queue_type                priority_queues
% 6.95/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.95/1.49  --res_passive_queues_freq               [15;5]
% 6.95/1.49  --res_forward_subs                      full
% 6.95/1.49  --res_backward_subs                     full
% 6.95/1.49  --res_forward_subs_resolution           true
% 6.95/1.49  --res_backward_subs_resolution          true
% 6.95/1.49  --res_orphan_elimination                true
% 6.95/1.49  --res_time_limit                        2.
% 6.95/1.49  --res_out_proof                         true
% 6.95/1.49  
% 6.95/1.49  ------ Superposition Options
% 6.95/1.49  
% 6.95/1.49  --superposition_flag                    true
% 6.95/1.49  --sup_passive_queue_type                priority_queues
% 6.95/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.95/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.95/1.49  --demod_completeness_check              fast
% 6.95/1.49  --demod_use_ground                      true
% 6.95/1.49  --sup_to_prop_solver                    passive
% 6.95/1.49  --sup_prop_simpl_new                    true
% 6.95/1.49  --sup_prop_simpl_given                  true
% 6.95/1.49  --sup_fun_splitting                     false
% 6.95/1.49  --sup_smt_interval                      50000
% 6.95/1.49  
% 6.95/1.49  ------ Superposition Simplification Setup
% 6.95/1.49  
% 6.95/1.49  --sup_indices_passive                   []
% 6.95/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.95/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_full_bw                           [BwDemod]
% 6.95/1.49  --sup_immed_triv                        [TrivRules]
% 6.95/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_immed_bw_main                     []
% 6.95/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.95/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.95/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.95/1.49  
% 6.95/1.49  ------ Combination Options
% 6.95/1.49  
% 6.95/1.49  --comb_res_mult                         3
% 6.95/1.49  --comb_sup_mult                         2
% 6.95/1.49  --comb_inst_mult                        10
% 6.95/1.49  
% 6.95/1.49  ------ Debug Options
% 6.95/1.49  
% 6.95/1.49  --dbg_backtrace                         false
% 6.95/1.49  --dbg_dump_prop_clauses                 false
% 6.95/1.49  --dbg_dump_prop_clauses_file            -
% 6.95/1.49  --dbg_out_stat                          false
% 6.95/1.49  ------ Parsing...
% 6.95/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.95/1.49  ------ Proving...
% 6.95/1.49  ------ Problem Properties 
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  clauses                                 32
% 6.95/1.49  conjectures                             2
% 6.95/1.49  EPR                                     4
% 6.95/1.49  Horn                                    25
% 6.95/1.49  unary                                   11
% 6.95/1.49  binary                                  16
% 6.95/1.49  lits                                    62
% 6.95/1.49  lits eq                                 18
% 6.95/1.49  fd_pure                                 0
% 6.95/1.49  fd_pseudo                               0
% 6.95/1.49  fd_cond                                 2
% 6.95/1.49  fd_pseudo_cond                          3
% 6.95/1.49  AC symbols                              0
% 6.95/1.49  
% 6.95/1.49  ------ Schedule dynamic 5 is on 
% 6.95/1.49  
% 6.95/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  Current options:
% 6.95/1.49  ------ 
% 6.95/1.49  
% 6.95/1.49  ------ Input Options
% 6.95/1.49  
% 6.95/1.49  --out_options                           all
% 6.95/1.49  --tptp_safe_out                         true
% 6.95/1.49  --problem_path                          ""
% 6.95/1.49  --include_path                          ""
% 6.95/1.49  --clausifier                            res/vclausify_rel
% 6.95/1.49  --clausifier_options                    --mode clausify
% 6.95/1.49  --stdin                                 false
% 6.95/1.49  --stats_out                             all
% 6.95/1.49  
% 6.95/1.49  ------ General Options
% 6.95/1.49  
% 6.95/1.49  --fof                                   false
% 6.95/1.49  --time_out_real                         305.
% 6.95/1.49  --time_out_virtual                      -1.
% 6.95/1.49  --symbol_type_check                     false
% 6.95/1.49  --clausify_out                          false
% 6.95/1.49  --sig_cnt_out                           false
% 6.95/1.49  --trig_cnt_out                          false
% 6.95/1.49  --trig_cnt_out_tolerance                1.
% 6.95/1.49  --trig_cnt_out_sk_spl                   false
% 6.95/1.49  --abstr_cl_out                          false
% 6.95/1.49  
% 6.95/1.49  ------ Global Options
% 6.95/1.49  
% 6.95/1.49  --schedule                              default
% 6.95/1.49  --add_important_lit                     false
% 6.95/1.49  --prop_solver_per_cl                    1000
% 6.95/1.49  --min_unsat_core                        false
% 6.95/1.49  --soft_assumptions                      false
% 6.95/1.49  --soft_lemma_size                       3
% 6.95/1.49  --prop_impl_unit_size                   0
% 6.95/1.49  --prop_impl_unit                        []
% 6.95/1.49  --share_sel_clauses                     true
% 6.95/1.49  --reset_solvers                         false
% 6.95/1.49  --bc_imp_inh                            [conj_cone]
% 6.95/1.49  --conj_cone_tolerance                   3.
% 6.95/1.49  --extra_neg_conj                        none
% 6.95/1.49  --large_theory_mode                     true
% 6.95/1.49  --prolific_symb_bound                   200
% 6.95/1.49  --lt_threshold                          2000
% 6.95/1.49  --clause_weak_htbl                      true
% 6.95/1.49  --gc_record_bc_elim                     false
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing Options
% 6.95/1.49  
% 6.95/1.49  --preprocessing_flag                    true
% 6.95/1.49  --time_out_prep_mult                    0.1
% 6.95/1.49  --splitting_mode                        input
% 6.95/1.49  --splitting_grd                         true
% 6.95/1.49  --splitting_cvd                         false
% 6.95/1.49  --splitting_cvd_svl                     false
% 6.95/1.49  --splitting_nvd                         32
% 6.95/1.49  --sub_typing                            true
% 6.95/1.49  --prep_gs_sim                           true
% 6.95/1.49  --prep_unflatten                        true
% 6.95/1.49  --prep_res_sim                          true
% 6.95/1.49  --prep_upred                            true
% 6.95/1.49  --prep_sem_filter                       exhaustive
% 6.95/1.49  --prep_sem_filter_out                   false
% 6.95/1.49  --pred_elim                             true
% 6.95/1.49  --res_sim_input                         true
% 6.95/1.49  --eq_ax_congr_red                       true
% 6.95/1.49  --pure_diseq_elim                       true
% 6.95/1.49  --brand_transform                       false
% 6.95/1.49  --non_eq_to_eq                          false
% 6.95/1.49  --prep_def_merge                        true
% 6.95/1.49  --prep_def_merge_prop_impl              false
% 6.95/1.49  --prep_def_merge_mbd                    true
% 6.95/1.49  --prep_def_merge_tr_red                 false
% 6.95/1.49  --prep_def_merge_tr_cl                  false
% 6.95/1.49  --smt_preprocessing                     true
% 6.95/1.49  --smt_ac_axioms                         fast
% 6.95/1.49  --preprocessed_out                      false
% 6.95/1.49  --preprocessed_stats                    false
% 6.95/1.49  
% 6.95/1.49  ------ Abstraction refinement Options
% 6.95/1.49  
% 6.95/1.49  --abstr_ref                             []
% 6.95/1.49  --abstr_ref_prep                        false
% 6.95/1.49  --abstr_ref_until_sat                   false
% 6.95/1.49  --abstr_ref_sig_restrict                funpre
% 6.95/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.95/1.49  --abstr_ref_under                       []
% 6.95/1.49  
% 6.95/1.49  ------ SAT Options
% 6.95/1.49  
% 6.95/1.49  --sat_mode                              false
% 6.95/1.49  --sat_fm_restart_options                ""
% 6.95/1.49  --sat_gr_def                            false
% 6.95/1.49  --sat_epr_types                         true
% 6.95/1.49  --sat_non_cyclic_types                  false
% 6.95/1.49  --sat_finite_models                     false
% 6.95/1.49  --sat_fm_lemmas                         false
% 6.95/1.49  --sat_fm_prep                           false
% 6.95/1.49  --sat_fm_uc_incr                        true
% 6.95/1.49  --sat_out_model                         small
% 6.95/1.49  --sat_out_clauses                       false
% 6.95/1.49  
% 6.95/1.49  ------ QBF Options
% 6.95/1.49  
% 6.95/1.49  --qbf_mode                              false
% 6.95/1.49  --qbf_elim_univ                         false
% 6.95/1.49  --qbf_dom_inst                          none
% 6.95/1.49  --qbf_dom_pre_inst                      false
% 6.95/1.49  --qbf_sk_in                             false
% 6.95/1.49  --qbf_pred_elim                         true
% 6.95/1.49  --qbf_split                             512
% 6.95/1.49  
% 6.95/1.49  ------ BMC1 Options
% 6.95/1.49  
% 6.95/1.49  --bmc1_incremental                      false
% 6.95/1.49  --bmc1_axioms                           reachable_all
% 6.95/1.49  --bmc1_min_bound                        0
% 6.95/1.49  --bmc1_max_bound                        -1
% 6.95/1.49  --bmc1_max_bound_default                -1
% 6.95/1.49  --bmc1_symbol_reachability              true
% 6.95/1.49  --bmc1_property_lemmas                  false
% 6.95/1.49  --bmc1_k_induction                      false
% 6.95/1.49  --bmc1_non_equiv_states                 false
% 6.95/1.49  --bmc1_deadlock                         false
% 6.95/1.49  --bmc1_ucm                              false
% 6.95/1.49  --bmc1_add_unsat_core                   none
% 6.95/1.49  --bmc1_unsat_core_children              false
% 6.95/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.95/1.49  --bmc1_out_stat                         full
% 6.95/1.49  --bmc1_ground_init                      false
% 6.95/1.49  --bmc1_pre_inst_next_state              false
% 6.95/1.49  --bmc1_pre_inst_state                   false
% 6.95/1.49  --bmc1_pre_inst_reach_state             false
% 6.95/1.49  --bmc1_out_unsat_core                   false
% 6.95/1.49  --bmc1_aig_witness_out                  false
% 6.95/1.49  --bmc1_verbose                          false
% 6.95/1.49  --bmc1_dump_clauses_tptp                false
% 6.95/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.95/1.49  --bmc1_dump_file                        -
% 6.95/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.95/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.95/1.49  --bmc1_ucm_extend_mode                  1
% 6.95/1.49  --bmc1_ucm_init_mode                    2
% 6.95/1.49  --bmc1_ucm_cone_mode                    none
% 6.95/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.95/1.49  --bmc1_ucm_relax_model                  4
% 6.95/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.95/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.95/1.49  --bmc1_ucm_layered_model                none
% 6.95/1.49  --bmc1_ucm_max_lemma_size               10
% 6.95/1.49  
% 6.95/1.49  ------ AIG Options
% 6.95/1.49  
% 6.95/1.49  --aig_mode                              false
% 6.95/1.49  
% 6.95/1.49  ------ Instantiation Options
% 6.95/1.49  
% 6.95/1.49  --instantiation_flag                    true
% 6.95/1.49  --inst_sos_flag                         false
% 6.95/1.49  --inst_sos_phase                        true
% 6.95/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.95/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.95/1.49  --inst_lit_sel_side                     none
% 6.95/1.49  --inst_solver_per_active                1400
% 6.95/1.49  --inst_solver_calls_frac                1.
% 6.95/1.49  --inst_passive_queue_type               priority_queues
% 6.95/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.95/1.49  --inst_passive_queues_freq              [25;2]
% 6.95/1.49  --inst_dismatching                      true
% 6.95/1.49  --inst_eager_unprocessed_to_passive     true
% 6.95/1.49  --inst_prop_sim_given                   true
% 6.95/1.49  --inst_prop_sim_new                     false
% 6.95/1.49  --inst_subs_new                         false
% 6.95/1.49  --inst_eq_res_simp                      false
% 6.95/1.49  --inst_subs_given                       false
% 6.95/1.49  --inst_orphan_elimination               true
% 6.95/1.49  --inst_learning_loop_flag               true
% 6.95/1.49  --inst_learning_start                   3000
% 6.95/1.49  --inst_learning_factor                  2
% 6.95/1.49  --inst_start_prop_sim_after_learn       3
% 6.95/1.49  --inst_sel_renew                        solver
% 6.95/1.49  --inst_lit_activity_flag                true
% 6.95/1.49  --inst_restr_to_given                   false
% 6.95/1.49  --inst_activity_threshold               500
% 6.95/1.49  --inst_out_proof                        true
% 6.95/1.49  
% 6.95/1.49  ------ Resolution Options
% 6.95/1.49  
% 6.95/1.49  --resolution_flag                       false
% 6.95/1.49  --res_lit_sel                           adaptive
% 6.95/1.49  --res_lit_sel_side                      none
% 6.95/1.49  --res_ordering                          kbo
% 6.95/1.49  --res_to_prop_solver                    active
% 6.95/1.49  --res_prop_simpl_new                    false
% 6.95/1.49  --res_prop_simpl_given                  true
% 6.95/1.49  --res_passive_queue_type                priority_queues
% 6.95/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.95/1.49  --res_passive_queues_freq               [15;5]
% 6.95/1.49  --res_forward_subs                      full
% 6.95/1.49  --res_backward_subs                     full
% 6.95/1.49  --res_forward_subs_resolution           true
% 6.95/1.49  --res_backward_subs_resolution          true
% 6.95/1.49  --res_orphan_elimination                true
% 6.95/1.49  --res_time_limit                        2.
% 6.95/1.49  --res_out_proof                         true
% 6.95/1.49  
% 6.95/1.49  ------ Superposition Options
% 6.95/1.49  
% 6.95/1.49  --superposition_flag                    true
% 6.95/1.49  --sup_passive_queue_type                priority_queues
% 6.95/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.95/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.95/1.49  --demod_completeness_check              fast
% 6.95/1.49  --demod_use_ground                      true
% 6.95/1.49  --sup_to_prop_solver                    passive
% 6.95/1.49  --sup_prop_simpl_new                    true
% 6.95/1.49  --sup_prop_simpl_given                  true
% 6.95/1.49  --sup_fun_splitting                     false
% 6.95/1.49  --sup_smt_interval                      50000
% 6.95/1.49  
% 6.95/1.49  ------ Superposition Simplification Setup
% 6.95/1.49  
% 6.95/1.49  --sup_indices_passive                   []
% 6.95/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.95/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.95/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_full_bw                           [BwDemod]
% 6.95/1.49  --sup_immed_triv                        [TrivRules]
% 6.95/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.95/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_immed_bw_main                     []
% 6.95/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.95/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.95/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.95/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.95/1.49  
% 6.95/1.49  ------ Combination Options
% 6.95/1.49  
% 6.95/1.49  --comb_res_mult                         3
% 6.95/1.49  --comb_sup_mult                         2
% 6.95/1.49  --comb_inst_mult                        10
% 6.95/1.49  
% 6.95/1.49  ------ Debug Options
% 6.95/1.49  
% 6.95/1.49  --dbg_backtrace                         false
% 6.95/1.49  --dbg_dump_prop_clauses                 false
% 6.95/1.49  --dbg_dump_prop_clauses_file            -
% 6.95/1.49  --dbg_out_stat                          false
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ Proving...
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS status Theorem for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49   Resolution empty clause
% 6.95/1.49  
% 6.95/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  fof(f3,axiom,(
% 6.95/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f27,plain,(
% 6.95/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.95/1.49    inference(rectify,[],[f3])).
% 6.95/1.49  
% 6.95/1.49  fof(f66,plain,(
% 6.95/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.95/1.49    inference(cnf_transformation,[],[f27])).
% 6.95/1.49  
% 6.95/1.49  fof(f11,axiom,(
% 6.95/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f31,plain,(
% 6.95/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 6.95/1.49    inference(ennf_transformation,[],[f11])).
% 6.95/1.49  
% 6.95/1.49  fof(f78,plain,(
% 6.95/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f31])).
% 6.95/1.49  
% 6.95/1.49  fof(f6,axiom,(
% 6.95/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f70,plain,(
% 6.95/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f6])).
% 6.95/1.49  
% 6.95/1.49  fof(f7,axiom,(
% 6.95/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f71,plain,(
% 6.95/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f7])).
% 6.95/1.49  
% 6.95/1.49  fof(f8,axiom,(
% 6.95/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f72,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f8])).
% 6.95/1.49  
% 6.95/1.49  fof(f9,axiom,(
% 6.95/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f73,plain,(
% 6.95/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f9])).
% 6.95/1.49  
% 6.95/1.49  fof(f106,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f72,f73])).
% 6.95/1.49  
% 6.95/1.49  fof(f107,plain,(
% 6.95/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f71,f106])).
% 6.95/1.49  
% 6.95/1.49  fof(f108,plain,(
% 6.95/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f70,f107])).
% 6.95/1.49  
% 6.95/1.49  fof(f109,plain,(
% 6.95/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f78,f108])).
% 6.95/1.49  
% 6.95/1.49  fof(f23,axiom,(
% 6.95/1.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f41,plain,(
% 6.95/1.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.95/1.49    inference(ennf_transformation,[],[f23])).
% 6.95/1.49  
% 6.95/1.49  fof(f42,plain,(
% 6.95/1.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.95/1.49    inference(flattening,[],[f41])).
% 6.95/1.49  
% 6.95/1.49  fof(f58,plain,(
% 6.95/1.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK3(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK3(X0),X0)))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f59,plain,(
% 6.95/1.49    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK3(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f58])).
% 6.95/1.49  
% 6.95/1.49  fof(f98,plain,(
% 6.95/1.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 6.95/1.49    inference(cnf_transformation,[],[f59])).
% 6.95/1.49  
% 6.95/1.49  fof(f4,axiom,(
% 6.95/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f28,plain,(
% 6.95/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.95/1.49    inference(rectify,[],[f4])).
% 6.95/1.49  
% 6.95/1.49  fof(f30,plain,(
% 6.95/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.95/1.49    inference(ennf_transformation,[],[f28])).
% 6.95/1.49  
% 6.95/1.49  fof(f51,plain,(
% 6.95/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f52,plain,(
% 6.95/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f51])).
% 6.95/1.49  
% 6.95/1.49  fof(f68,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 6.95/1.49    inference(cnf_transformation,[],[f52])).
% 6.95/1.49  
% 6.95/1.49  fof(f24,axiom,(
% 6.95/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f43,plain,(
% 6.95/1.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 6.95/1.49    inference(ennf_transformation,[],[f24])).
% 6.95/1.49  
% 6.95/1.49  fof(f44,plain,(
% 6.95/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 6.95/1.49    inference(flattening,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f100,plain,(
% 6.95/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f44])).
% 6.95/1.49  
% 6.95/1.49  fof(f25,conjecture,(
% 6.95/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f26,negated_conjecture,(
% 6.95/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 6.95/1.49    inference(negated_conjecture,[],[f25])).
% 6.95/1.49  
% 6.95/1.49  fof(f45,plain,(
% 6.95/1.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 6.95/1.49    inference(ennf_transformation,[],[f26])).
% 6.95/1.49  
% 6.95/1.49  fof(f46,plain,(
% 6.95/1.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 6.95/1.49    inference(flattening,[],[f45])).
% 6.95/1.49  
% 6.95/1.49  fof(f60,plain,(
% 6.95/1.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK6,sK4),sK5) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f61,plain,(
% 6.95/1.49    ~r2_hidden(k1_funct_1(sK6,sK4),sK5) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6)),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f60])).
% 6.95/1.49  
% 6.95/1.49  fof(f102,plain,(
% 6.95/1.49    v1_funct_2(sK6,k1_tarski(sK4),sK5)),
% 6.95/1.49    inference(cnf_transformation,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f112,plain,(
% 6.95/1.49    v1_funct_2(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)),
% 6.95/1.49    inference(definition_unfolding,[],[f102,f108])).
% 6.95/1.49  
% 6.95/1.49  fof(f101,plain,(
% 6.95/1.49    v1_funct_1(sK6)),
% 6.95/1.49    inference(cnf_transformation,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f103,plain,(
% 6.95/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))),
% 6.95/1.49    inference(cnf_transformation,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f111,plain,(
% 6.95/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)))),
% 6.95/1.49    inference(definition_unfolding,[],[f103,f108])).
% 6.95/1.49  
% 6.95/1.49  fof(f104,plain,(
% 6.95/1.49    k1_xboole_0 != sK5),
% 6.95/1.49    inference(cnf_transformation,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f105,plain,(
% 6.95/1.49    ~r2_hidden(k1_funct_1(sK6,sK4),sK5)),
% 6.95/1.49    inference(cnf_transformation,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f2,axiom,(
% 6.95/1.49    v1_xboole_0(k1_xboole_0)),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f65,plain,(
% 6.95/1.49    v1_xboole_0(k1_xboole_0)),
% 6.95/1.49    inference(cnf_transformation,[],[f2])).
% 6.95/1.49  
% 6.95/1.49  fof(f14,axiom,(
% 6.95/1.49    ! [X0,X1,X2] : ~v1_xboole_0(k1_enumset1(X0,X1,X2))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f82,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X1,X2))) )),
% 6.95/1.49    inference(cnf_transformation,[],[f14])).
% 6.95/1.49  
% 6.95/1.49  fof(f110,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(k3_enumset1(X0,X0,X0,X1,X2))) )),
% 6.95/1.49    inference(definition_unfolding,[],[f82,f106])).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4,plain,
% 6.95/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 6.95/1.49      inference(cnf_transformation,[],[f66]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_12,plain,
% 6.95/1.49      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f109]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1915,plain,
% 6.95/1.49      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 6.95/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_33,plain,
% 6.95/1.49      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 6.95/1.49      inference(cnf_transformation,[],[f98]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1910,plain,
% 6.95/1.49      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_5,plain,
% 6.95/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 6.95/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1922,plain,
% 6.95/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 6.95/1.49      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3946,plain,
% 6.95/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1910,c_1922]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_6152,plain,
% 6.95/1.49      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k1_xboole_0
% 6.95/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1915,c_3946]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_34,plain,
% 6.95/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.95/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.95/1.49      | ~ r2_hidden(X3,X1)
% 6.95/1.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 6.95/1.49      | ~ v1_funct_1(X0)
% 6.95/1.49      | k1_xboole_0 = X2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f100]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_38,negated_conjecture,
% 6.95/1.49      ( v1_funct_2(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
% 6.95/1.49      inference(cnf_transformation,[],[f112]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_463,plain,
% 6.95/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.95/1.49      | ~ r2_hidden(X3,X1)
% 6.95/1.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 6.95/1.49      | ~ v1_funct_1(X0)
% 6.95/1.49      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1
% 6.95/1.49      | sK5 != X2
% 6.95/1.49      | sK6 != X0
% 6.95/1.49      | k1_xboole_0 = X2 ),
% 6.95/1.49      inference(resolution_lifted,[status(thm)],[c_34,c_38]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_464,plain,
% 6.95/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)))
% 6.95/1.49      | ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 6.95/1.49      | r2_hidden(k1_funct_1(sK6,X0),sK5)
% 6.95/1.49      | ~ v1_funct_1(sK6)
% 6.95/1.49      | k1_xboole_0 = sK5 ),
% 6.95/1.49      inference(unflattening,[status(thm)],[c_463]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_39,negated_conjecture,
% 6.95/1.49      ( v1_funct_1(sK6) ),
% 6.95/1.49      inference(cnf_transformation,[],[f101]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_37,negated_conjecture,
% 6.95/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5))) ),
% 6.95/1.49      inference(cnf_transformation,[],[f111]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_36,negated_conjecture,
% 6.95/1.49      ( k1_xboole_0 != sK5 ),
% 6.95/1.49      inference(cnf_transformation,[],[f104]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_468,plain,
% 6.95/1.49      ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 6.95/1.49      | r2_hidden(k1_funct_1(sK6,X0),sK5) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_464,c_39,c_37,c_36]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1908,plain,
% 6.95/1.49      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 6.95/1.49      | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_18829,plain,
% 6.95/1.49      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0
% 6.95/1.49      | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_6152,c_1908]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_35,negated_conjecture,
% 6.95/1.49      ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5) ),
% 6.95/1.49      inference(cnf_transformation,[],[f105]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1909,plain,
% 6.95/1.49      ( r2_hidden(k1_funct_1(sK6,sK4),sK5) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_19223,plain,
% 6.95/1.49      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_18829,c_1909]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_19412,plain,
% 6.95/1.49      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_4,c_19223]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3,plain,
% 6.95/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f65]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_16,plain,
% 6.95/1.49      ( ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X1,X2)) ),
% 6.95/1.49      inference(cnf_transformation,[],[f110]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_501,plain,
% 6.95/1.49      ( k3_enumset1(X0,X0,X0,X1,X2) != k1_xboole_0 ),
% 6.95/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_19443,plain,
% 6.95/1.49      ( $false ),
% 6.95/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_19412,c_501]) ).
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  ------                               Statistics
% 6.95/1.49  
% 6.95/1.49  ------ General
% 6.95/1.49  
% 6.95/1.49  abstr_ref_over_cycles:                  0
% 6.95/1.49  abstr_ref_under_cycles:                 0
% 6.95/1.49  gc_basic_clause_elim:                   0
% 6.95/1.49  forced_gc_time:                         0
% 6.95/1.49  parsing_time:                           0.012
% 6.95/1.49  unif_index_cands_time:                  0.
% 6.95/1.49  unif_index_add_time:                    0.
% 6.95/1.49  orderings_time:                         0.
% 6.95/1.49  out_proof_time:                         0.008
% 6.95/1.49  total_time:                             0.529
% 6.95/1.49  num_of_symbols:                         56
% 6.95/1.49  num_of_terms:                           17852
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing
% 6.95/1.49  
% 6.95/1.49  num_of_splits:                          0
% 6.95/1.49  num_of_split_atoms:                     0
% 6.95/1.49  num_of_reused_defs:                     0
% 6.95/1.49  num_eq_ax_congr_red:                    36
% 6.95/1.49  num_of_sem_filtered_clauses:            1
% 6.95/1.49  num_of_subtypes:                        0
% 6.95/1.49  monotx_restored_types:                  0
% 6.95/1.49  sat_num_of_epr_types:                   0
% 6.95/1.49  sat_num_of_non_cyclic_types:            0
% 6.95/1.49  sat_guarded_non_collapsed_types:        0
% 6.95/1.49  num_pure_diseq_elim:                    0
% 6.95/1.49  simp_replaced_by:                       0
% 6.95/1.49  res_preprocessed:                       160
% 6.95/1.49  prep_upred:                             0
% 6.95/1.49  prep_unflattend:                        73
% 6.95/1.49  smt_new_axioms:                         0
% 6.95/1.49  pred_elim_cands:                        3
% 6.95/1.49  pred_elim:                              5
% 6.95/1.49  pred_elim_cl:                           7
% 6.95/1.49  pred_elim_cycles:                       7
% 6.95/1.49  merged_defs:                            8
% 6.95/1.49  merged_defs_ncl:                        0
% 6.95/1.49  bin_hyper_res:                          8
% 6.95/1.49  prep_cycles:                            4
% 6.95/1.49  pred_elim_time:                         0.014
% 6.95/1.49  splitting_time:                         0.
% 6.95/1.49  sem_filter_time:                        0.
% 6.95/1.49  monotx_time:                            0.
% 6.95/1.49  subtype_inf_time:                       0.
% 6.95/1.49  
% 6.95/1.49  ------ Problem properties
% 6.95/1.49  
% 6.95/1.49  clauses:                                32
% 6.95/1.49  conjectures:                            2
% 6.95/1.49  epr:                                    4
% 6.95/1.49  horn:                                   25
% 6.95/1.49  ground:                                 5
% 6.95/1.49  unary:                                  11
% 6.95/1.49  binary:                                 16
% 6.95/1.49  lits:                                   62
% 6.95/1.49  lits_eq:                                18
% 6.95/1.49  fd_pure:                                0
% 6.95/1.49  fd_pseudo:                              0
% 6.95/1.49  fd_cond:                                2
% 6.95/1.49  fd_pseudo_cond:                         3
% 6.95/1.49  ac_symbols:                             0
% 6.95/1.49  
% 6.95/1.49  ------ Propositional Solver
% 6.95/1.49  
% 6.95/1.49  prop_solver_calls:                      29
% 6.95/1.49  prop_fast_solver_calls:                 1213
% 6.95/1.49  smt_solver_calls:                       0
% 6.95/1.49  smt_fast_solver_calls:                  0
% 6.95/1.49  prop_num_of_clauses:                    7091
% 6.95/1.49  prop_preprocess_simplified:             16643
% 6.95/1.49  prop_fo_subsumed:                       8
% 6.95/1.49  prop_solver_time:                       0.
% 6.95/1.49  smt_solver_time:                        0.
% 6.95/1.49  smt_fast_solver_time:                   0.
% 6.95/1.49  prop_fast_solver_time:                  0.
% 6.95/1.49  prop_unsat_core_time:                   0.
% 6.95/1.49  
% 6.95/1.49  ------ QBF
% 6.95/1.49  
% 6.95/1.49  qbf_q_res:                              0
% 6.95/1.49  qbf_num_tautologies:                    0
% 6.95/1.49  qbf_prep_cycles:                        0
% 6.95/1.49  
% 6.95/1.49  ------ BMC1
% 6.95/1.49  
% 6.95/1.49  bmc1_current_bound:                     -1
% 6.95/1.49  bmc1_last_solved_bound:                 -1
% 6.95/1.49  bmc1_unsat_core_size:                   -1
% 6.95/1.49  bmc1_unsat_core_parents_size:           -1
% 6.95/1.49  bmc1_merge_next_fun:                    0
% 6.95/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.95/1.49  
% 6.95/1.49  ------ Instantiation
% 6.95/1.49  
% 6.95/1.49  inst_num_of_clauses:                    1780
% 6.95/1.49  inst_num_in_passive:                    947
% 6.95/1.49  inst_num_in_active:                     697
% 6.95/1.49  inst_num_in_unprocessed:                136
% 6.95/1.49  inst_num_of_loops:                      800
% 6.95/1.49  inst_num_of_learning_restarts:          0
% 6.95/1.49  inst_num_moves_active_passive:          101
% 6.95/1.49  inst_lit_activity:                      0
% 6.95/1.49  inst_lit_activity_moves:                0
% 6.95/1.49  inst_num_tautologies:                   0
% 6.95/1.49  inst_num_prop_implied:                  0
% 6.95/1.49  inst_num_existing_simplified:           0
% 6.95/1.49  inst_num_eq_res_simplified:             0
% 6.95/1.49  inst_num_child_elim:                    0
% 6.95/1.49  inst_num_of_dismatching_blockings:      713
% 6.95/1.49  inst_num_of_non_proper_insts:           1404
% 6.95/1.49  inst_num_of_duplicates:                 0
% 6.95/1.49  inst_inst_num_from_inst_to_res:         0
% 6.95/1.49  inst_dismatching_checking_time:         0.
% 6.95/1.49  
% 6.95/1.49  ------ Resolution
% 6.95/1.49  
% 6.95/1.49  res_num_of_clauses:                     0
% 6.95/1.49  res_num_in_passive:                     0
% 6.95/1.49  res_num_in_active:                      0
% 6.95/1.49  res_num_of_loops:                       164
% 6.95/1.49  res_forward_subset_subsumed:            60
% 6.95/1.49  res_backward_subset_subsumed:           0
% 6.95/1.49  res_forward_subsumed:                   0
% 6.95/1.49  res_backward_subsumed:                  1
% 6.95/1.49  res_forward_subsumption_resolution:     4
% 6.95/1.49  res_backward_subsumption_resolution:    0
% 6.95/1.49  res_clause_to_clause_subsumption:       2558
% 6.95/1.49  res_orphan_elimination:                 0
% 6.95/1.49  res_tautology_del:                      106
% 6.95/1.49  res_num_eq_res_simplified:              0
% 6.95/1.49  res_num_sel_changes:                    0
% 6.95/1.49  res_moves_from_active_to_pass:          0
% 6.95/1.49  
% 6.95/1.49  ------ Superposition
% 6.95/1.49  
% 6.95/1.49  sup_time_total:                         0.
% 6.95/1.49  sup_time_generating:                    0.
% 6.95/1.49  sup_time_sim_full:                      0.
% 6.95/1.49  sup_time_sim_immed:                     0.
% 6.95/1.49  
% 6.95/1.49  sup_num_of_clauses:                     537
% 6.95/1.49  sup_num_in_active:                      158
% 6.95/1.49  sup_num_in_passive:                     379
% 6.95/1.49  sup_num_of_loops:                       159
% 6.95/1.49  sup_fw_superposition:                   280
% 6.95/1.49  sup_bw_superposition:                   357
% 6.95/1.49  sup_immediate_simplified:               33
% 6.95/1.49  sup_given_eliminated:                   1
% 6.95/1.49  comparisons_done:                       0
% 6.95/1.49  comparisons_avoided:                    4
% 6.95/1.49  
% 6.95/1.49  ------ Simplifications
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  sim_fw_subset_subsumed:                 22
% 6.95/1.49  sim_bw_subset_subsumed:                 3
% 6.95/1.49  sim_fw_subsumed:                        3
% 6.95/1.49  sim_bw_subsumed:                        4
% 6.95/1.49  sim_fw_subsumption_res:                 2
% 6.95/1.49  sim_bw_subsumption_res:                 0
% 6.95/1.49  sim_tautology_del:                      8
% 6.95/1.49  sim_eq_tautology_del:                   2
% 6.95/1.49  sim_eq_res_simp:                        0
% 6.95/1.49  sim_fw_demodulated:                     4
% 6.95/1.49  sim_bw_demodulated:                     4
% 6.95/1.49  sim_light_normalised:                   7
% 6.95/1.49  sim_joinable_taut:                      0
% 6.95/1.49  sim_joinable_simp:                      0
% 6.95/1.49  sim_ac_normalised:                      0
% 6.95/1.49  sim_smt_subsumption:                    0
% 6.95/1.49  
%------------------------------------------------------------------------------
