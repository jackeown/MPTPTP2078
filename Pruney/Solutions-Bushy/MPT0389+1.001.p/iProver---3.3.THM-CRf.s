%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:11 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 159 expanded)
%              Number of clauses        :   52 (  56 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  343 ( 668 expanded)
%              Number of equality atoms :   95 ( 189 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK0(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK0(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
                  & r2_hidden(sK1(X0,X1),X0) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK0(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK2(X0,X5))
                    & r2_hidden(sK2(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f41,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f35])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5))
      & k1_xboole_0 != sK5
      & r1_tarski(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5))
    & k1_xboole_0 != sK5
    & r1_tarski(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f38])).

fof(f63,plain,(
    ~ r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_939,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2464,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_7421,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_7423,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_7421])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2396,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(sK6))
    | ~ r2_hidden(X1,sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5480,plain,
    ( r2_hidden(X0,sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))))
    | ~ r2_hidden(X0,k1_setfam_1(sK6))
    | ~ r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_6463,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))))
    | ~ r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),k1_setfam_1(sK6))
    | ~ r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_5480])).

cnf(c_938,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3284,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_943,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2782,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_2784,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1655,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),X0)
    | ~ r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2180,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK5)
    | r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK6) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_169])).

cnf(c_1630,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ r2_hidden(sK4(sK5),sK5)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_2173,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK4(sK5),sK5)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1292,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1291,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1601,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1292,c_1291])).

cnf(c_1603,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1601,c_1292])).

cnf(c_1604,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1603])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1470,plain,
    ( ~ r2_hidden(X0,sK2(sK5,X0))
    | r2_hidden(X0,k1_setfam_1(sK5))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1576,plain,
    ( ~ r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))))
    | r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),k1_setfam_1(sK5))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1475,plain,
    ( r2_hidden(X0,k1_setfam_1(sK5))
    | r2_hidden(sK2(sK5,X0),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1562,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),k1_setfam_1(sK5))
    | r2_hidden(sK2(sK5,sK3(k1_setfam_1(sK6),k1_setfam_1(sK5))),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_13,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_283,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK4(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_284,plain,
    ( r2_hidden(sK4(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_1514,plain,
    ( r2_hidden(sK4(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_1452,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_458,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k1_setfam_1(sK5) != X1
    | k1_setfam_1(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_459,plain,
    ( ~ r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),k1_setfam_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_451,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k1_setfam_1(sK5) != X1
    | k1_setfam_1(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_452,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK6),k1_setfam_1(sK5)),k1_setfam_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7423,c_6463,c_3284,c_2784,c_2180,c_2173,c_1604,c_1576,c_1562,c_1514,c_1452,c_459,c_452,c_22,c_23])).


%------------------------------------------------------------------------------
