%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0344+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:03 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 212 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f19,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK2)
          | ~ m1_subset_1(X2,sK1) )
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,sK1) )
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).

fof(f29,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_240,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_617,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_61,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_1])).

cnf(c_62,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_61])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK2)
    | X2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_8])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_576,plain,
    ( ~ r2_hidden(sK0(sK2),sK1)
    | ~ r2_hidden(sK0(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_195,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_503,plain,
    ( r2_hidden(sK0(sK2),X0)
    | ~ r2_hidden(sK0(sK2),sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_575,plain,
    ( r2_hidden(sK0(sK2),sK1)
    | ~ r2_hidden(sK0(sK2),sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_33,plain,
    ( r2_hidden(sK0(sK2),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_617,c_576,c_575,c_33,c_16,c_9])).


%------------------------------------------------------------------------------
