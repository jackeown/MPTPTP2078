%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0370+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:08 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of clauses        :   46 (  48 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  329 ( 759 expanded)
%              Number of equality atoms :   65 ( 129 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK3) != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | r2_hidden(X3,sK3) )
              & ( ~ r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | r2_hidden(X3,X2) )
                  & ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK1,X2) != sK2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK2)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK2) ) )
              | ~ m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_subset_1(sK1,sK3) != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | r2_hidden(X3,sK3) )
          & ( ~ r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f22,f21])).

fof(f40,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    k3_subset_1(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(X0,sK2)
    | r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26098,plain,
    ( r2_hidden(sK0(X0,X1,X2),sK2)
    | r2_hidden(sK0(X0,X1,X2),sK3)
    | ~ m1_subset_1(sK0(X0,X1,X2),sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_26322,plain,
    ( r2_hidden(sK0(X0,X1,sK2),sK2)
    | r2_hidden(sK0(X0,X1,sK2),sK3)
    | ~ m1_subset_1(sK0(X0,X1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_26098])).

cnf(c_27542,plain,
    ( r2_hidden(sK0(X0,sK3,sK2),sK2)
    | r2_hidden(sK0(X0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK0(X0,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_26322])).

cnf(c_27544,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | ~ m1_subset_1(sK0(sK1,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_27542])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_121,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_12])).

cnf(c_122,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_121])).

cnf(c_25735,plain,
    ( ~ r2_hidden(sK0(X0,sK3,X1),sK1)
    | m1_subset_1(sK0(X0,sK3,X1),sK1) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_27123,plain,
    ( ~ r2_hidden(sK0(X0,sK3,sK2),sK1)
    | m1_subset_1(sK0(X0,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_25735])).

cnf(c_27125,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK1)
    | m1_subset_1(sK0(sK1,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_27123])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_26890,plain,
    ( ~ r2_hidden(sK0(X0,sK3,sK2),X0)
    | ~ r2_hidden(sK0(X0,sK3,sK2),sK2)
    | r2_hidden(sK0(X0,sK3,sK2),sK3)
    | k4_xboole_0(X0,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_26892,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK1)
    | k4_xboole_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_26890])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26097,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),sK2)
    | ~ r2_hidden(sK0(X0,X1,X2),sK3)
    | ~ m1_subset_1(sK0(X0,X1,X2),sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_26630,plain,
    ( ~ r2_hidden(sK0(X0,sK3,X1),sK2)
    | ~ r2_hidden(sK0(X0,sK3,X1),sK3)
    | ~ m1_subset_1(sK0(X0,sK3,X1),sK1) ),
    inference(instantiation,[status(thm)],[c_26097])).

cnf(c_26665,plain,
    ( ~ r2_hidden(sK0(X0,sK3,sK2),sK2)
    | ~ r2_hidden(sK0(X0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK0(X0,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_26630])).

cnf(c_26667,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | ~ m1_subset_1(sK0(sK1,sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_26665])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15893,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_16078,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK2),sK2)
    | r2_hidden(sK0(X0,X1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15893])).

cnf(c_20270,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | r2_hidden(sK0(sK1,sK3,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16078])).

cnf(c_160,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13990,plain,
    ( k4_xboole_0(sK1,sK3) != X0
    | sK2 != X0
    | sK2 = k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_18997,plain,
    ( k4_xboole_0(sK1,sK3) != sK2
    | sK2 = k4_xboole_0(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_13990])).

cnf(c_18998,plain,
    ( k4_xboole_0(sK1,sK3) != sK2
    | sK2 = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_18997])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16163,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK2),X1)
    | r2_hidden(sK0(X0,X1,sK2),sK2)
    | k4_xboole_0(X0,X1) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16604,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | k4_xboole_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_16163])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16164,plain,
    ( r2_hidden(sK0(X0,X1,sK2),X0)
    | r2_hidden(sK0(X0,X1,sK2),sK2)
    | k4_xboole_0(X0,X1) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16585,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | r2_hidden(sK0(sK1,sK3,sK2),sK1)
    | k4_xboole_0(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_16164])).

cnf(c_13774,plain,
    ( k3_subset_1(sK1,sK3) != X0
    | k3_subset_1(sK1,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_13950,plain,
    ( k3_subset_1(sK1,sK3) != k4_xboole_0(sK1,sK3)
    | k3_subset_1(sK1,sK3) = sK2
    | sK2 != k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_13774])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13865,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13790,plain,
    ( X0 != X1
    | k3_subset_1(sK1,sK3) != X1
    | k3_subset_1(sK1,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_13855,plain,
    ( X0 != k3_subset_1(sK1,sK3)
    | k3_subset_1(sK1,sK3) = X0
    | k3_subset_1(sK1,sK3) != k3_subset_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_13790])).

cnf(c_13856,plain,
    ( X0 != k3_subset_1(sK1,sK3)
    | k3_subset_1(sK1,sK3) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13855])).

cnf(c_13859,plain,
    ( k4_xboole_0(sK1,sK3) != k3_subset_1(sK1,sK3)
    | k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_13856])).

cnf(c_13,negated_conjecture,
    ( k3_subset_1(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27544,c_27125,c_26892,c_26667,c_20270,c_18998,c_16604,c_16585,c_13950,c_13865,c_13859,c_13,c_16,c_17])).


%------------------------------------------------------------------------------
