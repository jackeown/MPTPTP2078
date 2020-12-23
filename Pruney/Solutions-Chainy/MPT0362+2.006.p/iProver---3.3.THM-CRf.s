%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:32 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 245 expanded)
%              Number of clauses        :   60 ( 111 expanded)
%              Number of leaves         :   16 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  269 ( 671 expanded)
%              Number of equality atoms :   43 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3)))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ~ r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f32])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1888,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
    | r1_tarski(X3,k3_xboole_0(X2,X1))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_212,c_0])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4966,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2))
    | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(resolution,[status(thm)],[c_1888,c_1])).

cnf(c_9390,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_4966,c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9593,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
    inference(resolution,[status(thm)],[c_9390,c_2])).

cnf(c_211,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_210,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2085,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_211,c_210])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3759,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2085,c_3])).

cnf(c_1902,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_212,c_210])).

cnf(c_3872,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_3759,c_1902])).

cnf(c_9619,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_9593,c_3872])).

cnf(c_1890,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X3,k3_xboole_0(X1,X2))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_212,c_3])).

cnf(c_6833,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_1890,c_210])).

cnf(c_9958,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_9619,c_6833])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1064,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_11,c_17])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_819,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1069,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_17,c_32,c_819])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1081,plain,
    ( r1_tarski(sK3,sK1) ),
    inference(resolution,[status(thm)],[c_1069,c_7])).

cnf(c_12072,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_9958,c_1081])).

cnf(c_4120,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_3872,c_1])).

cnf(c_4150,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_4120,c_1])).

cnf(c_4990,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2))
    | X0 != k3_xboole_0(X2,X1) ),
    inference(resolution,[status(thm)],[c_1888,c_4150])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k9_subset_1(X1,X2,X0),k3_xboole_0(X0,X2)) ),
    inference(resolution,[status(thm)],[c_4990,c_13])).

cnf(c_6300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k9_subset_1(X1,X2,X0),X0) ),
    inference(resolution,[status(thm)],[c_5542,c_2])).

cnf(c_12236,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(k9_subset_1(X0,X1,sK3),sK1) ),
    inference(resolution,[status(thm)],[c_12072,c_6300])).

cnf(c_1914,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_1902,c_0])).

cnf(c_4299,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_4150,c_1914])).

cnf(c_5012,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2))
    | X0 != k3_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_1888,c_4299])).

cnf(c_5716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k9_subset_1(X1,X2,X0),k3_xboole_0(X2,X0)) ),
    inference(resolution,[status(thm)],[c_5012,c_13])).

cnf(c_7290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k9_subset_1(X1,X2,X0),X2) ),
    inference(resolution,[status(thm)],[c_5716,c_2])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3664,plain,
    ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_16,c_15])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_629,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1167,plain,
    ( m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_629])).

cnf(c_1185,plain,
    ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1167])).

cnf(c_3847,plain,
    ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_18,c_1185])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6926,plain,
    ( ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_3847,c_10])).

cnf(c_7098,plain,
    ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
    | ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6926,c_32])).

cnf(c_7099,plain,
    ( ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_7098])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7114,plain,
    ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
    inference(resolution,[status(thm)],[c_7099,c_6])).

cnf(c_7315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
    inference(resolution,[status(thm)],[c_7290,c_7114])).

cnf(c_7552,plain,
    ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7315,c_17])).

cnf(c_18744,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_12236,c_7552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18744,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.96/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.99  
% 3.96/0.99  ------  iProver source info
% 3.96/0.99  
% 3.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.99  git: non_committed_changes: false
% 3.96/0.99  git: last_make_outside_of_git: false
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  ------ Parsing...
% 3.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.99  ------ Proving...
% 3.96/0.99  ------ Problem Properties 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  clauses                                 19
% 3.96/0.99  conjectures                             3
% 3.96/0.99  EPR                                     4
% 3.96/0.99  Horn                                    16
% 3.96/0.99  unary                                   6
% 3.96/0.99  binary                                  5
% 3.96/0.99  lits                                    42
% 3.96/0.99  lits eq                                 5
% 3.96/0.99  fd_pure                                 0
% 3.96/0.99  fd_pseudo                               0
% 3.96/0.99  fd_cond                                 0
% 3.96/0.99  fd_pseudo_cond                          2
% 3.96/0.99  AC symbols                              0
% 3.96/0.99  
% 3.96/0.99  ------ Input Options Time Limit: Unbounded
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  Current options:
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ Proving...
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS status Theorem for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  fof(f1,axiom,(
% 3.96/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f27,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f1])).
% 3.96/0.99  
% 3.96/0.99  fof(f2,axiom,(
% 3.96/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f28,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f2])).
% 3.96/0.99  
% 3.96/0.99  fof(f3,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f12,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.96/0.99    inference(ennf_transformation,[],[f3])).
% 3.96/0.99  
% 3.96/0.99  fof(f29,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f4,axiom,(
% 3.96/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f13,plain,(
% 3.96/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f4])).
% 3.96/0.99  
% 3.96/0.99  fof(f30,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f13])).
% 3.96/0.99  
% 3.96/0.99  fof(f6,axiom,(
% 3.96/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f14,plain,(
% 3.96/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f6])).
% 3.96/0.99  
% 3.96/0.99  fof(f22,plain,(
% 3.96/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.96/0.99    inference(nnf_transformation,[],[f14])).
% 3.96/0.99  
% 3.96/0.99  fof(f35,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f10,conjecture,(
% 3.96/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f11,negated_conjecture,(
% 3.96/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 3.96/0.99    inference(negated_conjecture,[],[f10])).
% 3.96/0.99  
% 3.96/0.99  fof(f17,plain,(
% 3.96/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f11])).
% 3.96/0.99  
% 3.96/0.99  fof(f25,plain,(
% 3.96/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f24,plain,(
% 3.96/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f26,plain,(
% 3.96/0.99    (~r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24])).
% 3.96/0.99  
% 3.96/0.99  fof(f44,plain,(
% 3.96/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.96/0.99    inference(cnf_transformation,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f7,axiom,(
% 3.96/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f39,plain,(
% 3.96/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f7])).
% 3.96/0.99  
% 3.96/0.99  fof(f5,axiom,(
% 3.96/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f18,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f5])).
% 3.96/0.99  
% 3.96/0.99  fof(f19,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.96/0.99    inference(rectify,[],[f18])).
% 3.96/0.99  
% 3.96/0.99  fof(f20,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f21,plain,(
% 3.96/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.96/0.99  
% 3.96/0.99  fof(f31,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f47,plain,(
% 3.96/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.96/0.99    inference(equality_resolution,[],[f31])).
% 3.96/0.99  
% 3.96/0.99  fof(f8,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f15,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f8])).
% 3.96/0.99  
% 3.96/0.99  fof(f40,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f15])).
% 3.96/0.99  
% 3.96/0.99  fof(f45,plain,(
% 3.96/0.99    ~r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3)))),
% 3.96/0.99    inference(cnf_transformation,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f9,axiom,(
% 3.96/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f16,plain,(
% 3.96/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f9])).
% 3.96/0.99  
% 3.96/0.99  fof(f23,plain,(
% 3.96/0.99    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.99    inference(nnf_transformation,[],[f16])).
% 3.96/0.99  
% 3.96/0.99  fof(f41,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  fof(f43,plain,(
% 3.96/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.96/0.99    inference(cnf_transformation,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f36,plain,(
% 3.96/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f32,plain,(
% 3.96/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f46,plain,(
% 3.96/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.96/0.99    inference(equality_resolution,[],[f32])).
% 3.96/0.99  
% 3.96/0.99  cnf(c_212,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_0,plain,
% 3.96/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1888,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
% 3.96/0.99      | r1_tarski(X3,k3_xboole_0(X2,X1))
% 3.96/0.99      | X3 != X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_212,c_0]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1,plain,
% 3.96/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4966,plain,
% 3.96/0.99      ( r1_tarski(X0,k3_xboole_0(X1,X2))
% 3.96/0.99      | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1888,c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9390,plain,
% 3.96/0.99      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4966,c_0]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2,plain,
% 3.96/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9593,plain,
% 3.96/0.99      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_9390,c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_211,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_210,plain,( X0 = X0 ),theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2085,plain,
% 3.96/0.99      ( X0 != X1 | X1 = X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_211,c_210]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3759,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_2085,c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1902,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_212,c_210]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3872,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1)
% 3.96/0.99      | r1_tarski(X0,X2)
% 3.96/0.99      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3759,c_1902]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9619,plain,
% 3.96/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_9593,c_3872]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1890,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1)
% 3.96/0.99      | ~ r1_tarski(X1,X2)
% 3.96/0.99      | r1_tarski(X3,k3_xboole_0(X1,X2))
% 3.96/0.99      | X3 != X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_212,c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6833,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1)
% 3.96/0.99      | ~ r1_tarski(X1,X2)
% 3.96/0.99      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1890,c_210]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9958,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_9619,c_6833]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_17,negated_conjecture,
% 3.96/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1064,plain,
% 3.96/0.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_11,c_17]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12,plain,
% 3.96/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_32,plain,
% 3.96/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_819,plain,
% 3.96/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.96/0.99      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 3.96/0.99      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1069,plain,
% 3.96/0.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_1064,c_17,c_32,c_819]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1081,plain,
% 3.96/0.99      ( r1_tarski(sK3,sK1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1069,c_7]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12072,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,sK3) | r1_tarski(X0,sK1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_9958,c_1081]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4120,plain,
% 3.96/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X0) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3872,c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4150,plain,
% 3.96/0.99      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4120,c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4990,plain,
% 3.96/0.99      ( r1_tarski(X0,k3_xboole_0(X1,X2)) | X0 != k3_xboole_0(X2,X1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1888,c_4150]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_13,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5542,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),k3_xboole_0(X0,X2)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4990,c_13]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6300,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),X0) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_5542,c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12236,plain,
% 3.96/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.96/0.99      | r1_tarski(k9_subset_1(X0,X1,sK3),sK1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_12072,c_6300]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1914,plain,
% 3.96/0.99      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
% 3.96/0.99      | r1_tarski(k3_xboole_0(X1,X0),X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1902,c_0]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4299,plain,
% 3.96/0.99      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4150,c_1914]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5012,plain,
% 3.96/0.99      ( r1_tarski(X0,k3_xboole_0(X1,X2)) | X0 != k3_xboole_0(X1,X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_1888,c_4299]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5716,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),k3_xboole_0(X2,X0)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_5012,c_13]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7290,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),X2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_5716,c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_16,negated_conjecture,
% 3.96/0.99      ( ~ r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) ),
% 3.96/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_15,plain,
% 3.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.96/0.99      | ~ r1_tarski(X2,X0)
% 3.96/0.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3664,plain,
% 3.96/0.99      ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_16,c_15]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18,negated_conjecture,
% 3.96/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_630,plain,
% 3.96/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.96/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.96/0.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_629,plain,
% 3.96/0.99      ( r1_tarski(k3_subset_1(sK1,sK2),k3_subset_1(sK1,k9_subset_1(sK1,sK2,sK3))) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1167,plain,
% 3.96/0.99      ( m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 3.96/0.99      | r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_630,c_629]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1185,plain,
% 3.96/0.99      ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
% 3.96/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1167]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3847,plain,
% 3.96/0.99      ( ~ m1_subset_1(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3664,c_18,c_1185]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10,plain,
% 3.96/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6926,plain,
% 3.96/0.99      ( ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
% 3.96/0.99      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3847,c_10]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7098,plain,
% 3.96/0.99      ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
% 3.96/0.99      | ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_6926,c_32]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7099,plain,
% 3.96/0.99      ( ~ r2_hidden(k9_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2) ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_7098]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6,plain,
% 3.96/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7114,plain,
% 3.96/0.99      ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK2)
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_7099,c_6]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7315,plain,
% 3.96/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.96/0.99      | ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_7290,c_7114]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7552,plain,
% 3.96/0.99      ( ~ r1_tarski(k9_subset_1(sK1,sK2,sK3),sK1) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_7315,c_17]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18744,plain,
% 3.96/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_12236,c_7552]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(contradiction,plain,
% 3.96/0.99      ( $false ),
% 3.96/0.99      inference(minisat,[status(thm)],[c_18744,c_17]) ).
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  ------                               Statistics
% 3.96/0.99  
% 3.96/0.99  ------ Selected
% 3.96/0.99  
% 3.96/0.99  total_time:                             0.477
% 3.96/0.99  
%------------------------------------------------------------------------------
