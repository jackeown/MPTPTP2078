%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:55 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 259 expanded)
%              Number of clauses        :   75 (  99 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  425 (1581 expanded)
%              Number of equality atoms :   70 (  71 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK2,X1)
          | r1_tsep_1(X1,sK2) )
        & m1_pre_topc(X1,sK2)
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK1)
              | r1_tsep_1(sK1,X2) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_832,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | r1_xboole_0(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1276,plain,
    ( r1_xboole_0(X0_43,X1_43)
    | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | X0_43 != u1_struct_0(sK1)
    | X1_43 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1532,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_xboole_0(k2_struct_0(sK1),X0_43)
    | X0_43 != u1_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_1621,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_231,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_232,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_232])).

cnf(c_288,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),X0)
    | ~ r1_xboole_0(k2_struct_0(sK1),X0)
    | ~ l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_815,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),X0_43)
    | ~ r1_xboole_0(k2_struct_0(sK1),X0_43)
    | ~ l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_1612,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_830,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1558,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_833,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1286,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_42))
    | X1_43 != u1_struct_0(X0_42)
    | X0_43 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1368,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | X0_43 != u1_struct_0(sK1)
    | X1_43 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1531,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tarski(k2_struct_0(sK1),X0_43)
    | X0_43 != u1_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1557,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tarski(k2_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_1487,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_831,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1396,plain,
    ( X0_43 != X1_43
    | X0_43 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1_43 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1461,plain,
    ( X0_43 = u1_struct_0(sK1)
    | X0_43 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_1486,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_828,plain,
    ( ~ l1_struct_0(X0_42)
    | u1_struct_0(X0_42) = k2_struct_0(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1462,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_7,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_823,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X1_42,X0_42)
    | ~ l1_struct_0(X0_42)
    | ~ l1_struct_0(X1_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1344,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_333,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_334,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_338,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_16])).

cnf(c_339,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_813,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | r1_tarski(u1_struct_0(X0_42),u1_struct_0(X1_42)) ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_1241,plain,
    ( ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_42)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_1325,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_10,negated_conjecture,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_822,negated_conjecture,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1110,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | r1_tsep_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_27,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | r1_tsep_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_827,plain,
    ( ~ l1_pre_topc(X0_42)
    | l1_struct_0(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1256,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1257,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_1259,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1260,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_1262,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1263,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top
    | r1_tsep_1(sK2,sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_826,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ l1_pre_topc(X1_42)
    | l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1292,plain,
    ( ~ m1_pre_topc(sK2,X0_42)
    | ~ l1_pre_topc(X0_42)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1293,plain,
    ( m1_pre_topc(sK2,X0_42) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_1295,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_1297,plain,
    ( ~ m1_pre_topc(sK1,X0_42)
    | ~ l1_pre_topc(X0_42)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1298,plain,
    ( m1_pre_topc(sK1,X0_42) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_1300,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_1304,plain,
    ( r1_tsep_1(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_21,c_23,c_25,c_27,c_1257,c_1260,c_1263,c_1295,c_1300])).

cnf(c_1306,plain,
    ( r1_tsep_1(sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1304])).

cnf(c_1299,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1294,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_6,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_824,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_xboole_0(u1_struct_0(X0_42),u1_struct_0(X1_42))
    | ~ l1_struct_0(X0_42)
    | ~ l1_struct_0(X1_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1265,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1621,c_1612,c_1558,c_1557,c_1487,c_1486,c_1462,c_1344,c_1325,c_1306,c_1299,c_1294,c_1265,c_1259,c_1256,c_11,c_12,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:21:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.93/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.93/0.99  
% 0.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.93/0.99  
% 0.93/0.99  ------  iProver source info
% 0.93/0.99  
% 0.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.93/0.99  git: non_committed_changes: false
% 0.93/0.99  git: last_make_outside_of_git: false
% 0.93/0.99  
% 0.93/0.99  ------ 
% 0.93/0.99  
% 0.93/0.99  ------ Input Options
% 0.93/0.99  
% 0.93/0.99  --out_options                           all
% 0.93/0.99  --tptp_safe_out                         true
% 0.93/0.99  --problem_path                          ""
% 0.93/0.99  --include_path                          ""
% 0.93/0.99  --clausifier                            res/vclausify_rel
% 0.93/0.99  --clausifier_options                    --mode clausify
% 0.93/0.99  --stdin                                 false
% 0.93/0.99  --stats_out                             all
% 0.93/0.99  
% 0.93/0.99  ------ General Options
% 0.93/0.99  
% 0.93/0.99  --fof                                   false
% 0.93/0.99  --time_out_real                         305.
% 0.93/0.99  --time_out_virtual                      -1.
% 0.93/0.99  --symbol_type_check                     false
% 0.93/0.99  --clausify_out                          false
% 0.93/0.99  --sig_cnt_out                           false
% 0.93/0.99  --trig_cnt_out                          false
% 0.93/0.99  --trig_cnt_out_tolerance                1.
% 0.93/0.99  --trig_cnt_out_sk_spl                   false
% 0.93/0.99  --abstr_cl_out                          false
% 0.93/0.99  
% 0.93/0.99  ------ Global Options
% 0.93/0.99  
% 0.93/0.99  --schedule                              default
% 0.93/0.99  --add_important_lit                     false
% 0.93/0.99  --prop_solver_per_cl                    1000
% 0.93/0.99  --min_unsat_core                        false
% 0.93/0.99  --soft_assumptions                      false
% 0.93/0.99  --soft_lemma_size                       3
% 0.93/0.99  --prop_impl_unit_size                   0
% 0.93/0.99  --prop_impl_unit                        []
% 0.93/0.99  --share_sel_clauses                     true
% 0.93/0.99  --reset_solvers                         false
% 0.93/0.99  --bc_imp_inh                            [conj_cone]
% 0.93/0.99  --conj_cone_tolerance                   3.
% 0.93/0.99  --extra_neg_conj                        none
% 0.93/0.99  --large_theory_mode                     true
% 0.93/0.99  --prolific_symb_bound                   200
% 0.93/0.99  --lt_threshold                          2000
% 0.93/0.99  --clause_weak_htbl                      true
% 0.93/0.99  --gc_record_bc_elim                     false
% 0.93/0.99  
% 0.93/0.99  ------ Preprocessing Options
% 0.93/0.99  
% 0.93/0.99  --preprocessing_flag                    true
% 0.93/0.99  --time_out_prep_mult                    0.1
% 0.93/0.99  --splitting_mode                        input
% 0.93/0.99  --splitting_grd                         true
% 0.93/0.99  --splitting_cvd                         false
% 0.93/0.99  --splitting_cvd_svl                     false
% 0.93/0.99  --splitting_nvd                         32
% 0.93/0.99  --sub_typing                            true
% 0.93/0.99  --prep_gs_sim                           true
% 0.93/0.99  --prep_unflatten                        true
% 0.93/0.99  --prep_res_sim                          true
% 0.93/0.99  --prep_upred                            true
% 0.93/0.99  --prep_sem_filter                       exhaustive
% 0.93/0.99  --prep_sem_filter_out                   false
% 0.93/0.99  --pred_elim                             true
% 0.93/0.99  --res_sim_input                         true
% 0.93/0.99  --eq_ax_congr_red                       true
% 0.93/0.99  --pure_diseq_elim                       true
% 0.93/0.99  --brand_transform                       false
% 0.93/0.99  --non_eq_to_eq                          false
% 0.93/0.99  --prep_def_merge                        true
% 0.93/0.99  --prep_def_merge_prop_impl              false
% 0.93/0.99  --prep_def_merge_mbd                    true
% 0.93/0.99  --prep_def_merge_tr_red                 false
% 0.93/0.99  --prep_def_merge_tr_cl                  false
% 0.93/0.99  --smt_preprocessing                     true
% 0.93/0.99  --smt_ac_axioms                         fast
% 0.93/0.99  --preprocessed_out                      false
% 0.93/0.99  --preprocessed_stats                    false
% 0.93/0.99  
% 0.93/0.99  ------ Abstraction refinement Options
% 0.93/0.99  
% 0.93/0.99  --abstr_ref                             []
% 0.93/0.99  --abstr_ref_prep                        false
% 0.93/0.99  --abstr_ref_until_sat                   false
% 0.93/0.99  --abstr_ref_sig_restrict                funpre
% 0.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/0.99  --abstr_ref_under                       []
% 0.93/0.99  
% 0.93/0.99  ------ SAT Options
% 0.93/0.99  
% 0.93/0.99  --sat_mode                              false
% 0.93/0.99  --sat_fm_restart_options                ""
% 0.93/0.99  --sat_gr_def                            false
% 0.93/0.99  --sat_epr_types                         true
% 0.93/0.99  --sat_non_cyclic_types                  false
% 0.93/0.99  --sat_finite_models                     false
% 0.93/0.99  --sat_fm_lemmas                         false
% 0.93/0.99  --sat_fm_prep                           false
% 0.93/0.99  --sat_fm_uc_incr                        true
% 0.93/0.99  --sat_out_model                         small
% 0.93/0.99  --sat_out_clauses                       false
% 0.93/0.99  
% 0.93/0.99  ------ QBF Options
% 0.93/0.99  
% 0.93/0.99  --qbf_mode                              false
% 0.93/0.99  --qbf_elim_univ                         false
% 0.93/0.99  --qbf_dom_inst                          none
% 0.93/0.99  --qbf_dom_pre_inst                      false
% 0.93/0.99  --qbf_sk_in                             false
% 0.93/0.99  --qbf_pred_elim                         true
% 0.93/0.99  --qbf_split                             512
% 0.93/0.99  
% 0.93/0.99  ------ BMC1 Options
% 0.93/0.99  
% 0.93/0.99  --bmc1_incremental                      false
% 0.93/0.99  --bmc1_axioms                           reachable_all
% 0.93/0.99  --bmc1_min_bound                        0
% 0.93/0.99  --bmc1_max_bound                        -1
% 0.93/0.99  --bmc1_max_bound_default                -1
% 0.93/0.99  --bmc1_symbol_reachability              true
% 0.93/0.99  --bmc1_property_lemmas                  false
% 0.93/0.99  --bmc1_k_induction                      false
% 0.93/0.99  --bmc1_non_equiv_states                 false
% 0.93/0.99  --bmc1_deadlock                         false
% 0.93/0.99  --bmc1_ucm                              false
% 0.93/0.99  --bmc1_add_unsat_core                   none
% 0.93/0.99  --bmc1_unsat_core_children              false
% 0.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/0.99  --bmc1_out_stat                         full
% 0.93/0.99  --bmc1_ground_init                      false
% 0.93/0.99  --bmc1_pre_inst_next_state              false
% 0.93/0.99  --bmc1_pre_inst_state                   false
% 0.93/0.99  --bmc1_pre_inst_reach_state             false
% 0.93/0.99  --bmc1_out_unsat_core                   false
% 0.93/0.99  --bmc1_aig_witness_out                  false
% 0.93/0.99  --bmc1_verbose                          false
% 0.93/0.99  --bmc1_dump_clauses_tptp                false
% 0.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.93/0.99  --bmc1_dump_file                        -
% 0.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.93/0.99  --bmc1_ucm_extend_mode                  1
% 0.93/0.99  --bmc1_ucm_init_mode                    2
% 0.93/0.99  --bmc1_ucm_cone_mode                    none
% 0.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.93/0.99  --bmc1_ucm_relax_model                  4
% 0.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/0.99  --bmc1_ucm_layered_model                none
% 0.93/0.99  --bmc1_ucm_max_lemma_size               10
% 0.93/0.99  
% 0.93/0.99  ------ AIG Options
% 0.93/0.99  
% 0.93/0.99  --aig_mode                              false
% 0.93/0.99  
% 0.93/0.99  ------ Instantiation Options
% 0.93/0.99  
% 0.93/0.99  --instantiation_flag                    true
% 0.93/0.99  --inst_sos_flag                         false
% 0.93/0.99  --inst_sos_phase                        true
% 0.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/0.99  --inst_lit_sel_side                     num_symb
% 0.93/0.99  --inst_solver_per_active                1400
% 0.93/0.99  --inst_solver_calls_frac                1.
% 0.93/0.99  --inst_passive_queue_type               priority_queues
% 0.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/0.99  --inst_passive_queues_freq              [25;2]
% 0.93/0.99  --inst_dismatching                      true
% 0.93/0.99  --inst_eager_unprocessed_to_passive     true
% 0.93/0.99  --inst_prop_sim_given                   true
% 0.93/0.99  --inst_prop_sim_new                     false
% 0.93/0.99  --inst_subs_new                         false
% 0.93/1.00  --inst_eq_res_simp                      false
% 0.93/1.00  --inst_subs_given                       false
% 0.93/1.00  --inst_orphan_elimination               true
% 0.93/1.00  --inst_learning_loop_flag               true
% 0.93/1.00  --inst_learning_start                   3000
% 0.93/1.00  --inst_learning_factor                  2
% 0.93/1.00  --inst_start_prop_sim_after_learn       3
% 0.93/1.00  --inst_sel_renew                        solver
% 0.93/1.00  --inst_lit_activity_flag                true
% 0.93/1.00  --inst_restr_to_given                   false
% 0.93/1.00  --inst_activity_threshold               500
% 0.93/1.00  --inst_out_proof                        true
% 0.93/1.00  
% 0.93/1.00  ------ Resolution Options
% 0.93/1.00  
% 0.93/1.00  --resolution_flag                       true
% 0.93/1.00  --res_lit_sel                           adaptive
% 0.93/1.00  --res_lit_sel_side                      none
% 0.93/1.00  --res_ordering                          kbo
% 0.93/1.00  --res_to_prop_solver                    active
% 0.93/1.00  --res_prop_simpl_new                    false
% 0.93/1.00  --res_prop_simpl_given                  true
% 0.93/1.00  --res_passive_queue_type                priority_queues
% 0.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.00  --res_passive_queues_freq               [15;5]
% 0.93/1.00  --res_forward_subs                      full
% 0.93/1.00  --res_backward_subs                     full
% 0.93/1.00  --res_forward_subs_resolution           true
% 0.93/1.00  --res_backward_subs_resolution          true
% 0.93/1.00  --res_orphan_elimination                true
% 0.93/1.00  --res_time_limit                        2.
% 0.93/1.00  --res_out_proof                         true
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Options
% 0.93/1.00  
% 0.93/1.00  --superposition_flag                    true
% 0.93/1.00  --sup_passive_queue_type                priority_queues
% 0.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.00  --demod_completeness_check              fast
% 0.93/1.00  --demod_use_ground                      true
% 0.93/1.00  --sup_to_prop_solver                    passive
% 0.93/1.00  --sup_prop_simpl_new                    true
% 0.93/1.00  --sup_prop_simpl_given                  true
% 0.93/1.00  --sup_fun_splitting                     false
% 0.93/1.00  --sup_smt_interval                      50000
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Simplification Setup
% 0.93/1.00  
% 0.93/1.00  --sup_indices_passive                   []
% 0.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_full_bw                           [BwDemod]
% 0.93/1.00  --sup_immed_triv                        [TrivRules]
% 0.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_immed_bw_main                     []
% 0.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  
% 0.93/1.00  ------ Combination Options
% 0.93/1.00  
% 0.93/1.00  --comb_res_mult                         3
% 0.93/1.00  --comb_sup_mult                         2
% 0.93/1.00  --comb_inst_mult                        10
% 0.93/1.00  
% 0.93/1.00  ------ Debug Options
% 0.93/1.00  
% 0.93/1.00  --dbg_backtrace                         false
% 0.93/1.00  --dbg_dump_prop_clauses                 false
% 0.93/1.00  --dbg_dump_prop_clauses_file            -
% 0.93/1.00  --dbg_out_stat                          false
% 0.93/1.00  ------ Parsing...
% 0.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.93/1.00  ------ Proving...
% 0.93/1.00  ------ Problem Properties 
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  clauses                                 16
% 0.93/1.00  conjectures                             5
% 0.93/1.00  EPR                                     8
% 0.93/1.00  Horn                                    15
% 0.93/1.00  unary                                   4
% 0.93/1.00  binary                                  4
% 0.93/1.00  lits                                    41
% 0.93/1.00  lits eq                                 1
% 0.93/1.00  fd_pure                                 0
% 0.93/1.00  fd_pseudo                               0
% 0.93/1.00  fd_cond                                 0
% 0.93/1.00  fd_pseudo_cond                          0
% 0.93/1.00  AC symbols                              0
% 0.93/1.00  
% 0.93/1.00  ------ Schedule dynamic 5 is on 
% 0.93/1.00  
% 0.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  ------ 
% 0.93/1.00  Current options:
% 0.93/1.00  ------ 
% 0.93/1.00  
% 0.93/1.00  ------ Input Options
% 0.93/1.00  
% 0.93/1.00  --out_options                           all
% 0.93/1.00  --tptp_safe_out                         true
% 0.93/1.00  --problem_path                          ""
% 0.93/1.00  --include_path                          ""
% 0.93/1.00  --clausifier                            res/vclausify_rel
% 0.93/1.00  --clausifier_options                    --mode clausify
% 0.93/1.00  --stdin                                 false
% 0.93/1.00  --stats_out                             all
% 0.93/1.00  
% 0.93/1.00  ------ General Options
% 0.93/1.00  
% 0.93/1.00  --fof                                   false
% 0.93/1.00  --time_out_real                         305.
% 0.93/1.00  --time_out_virtual                      -1.
% 0.93/1.00  --symbol_type_check                     false
% 0.93/1.00  --clausify_out                          false
% 0.93/1.00  --sig_cnt_out                           false
% 0.93/1.00  --trig_cnt_out                          false
% 0.93/1.00  --trig_cnt_out_tolerance                1.
% 0.93/1.00  --trig_cnt_out_sk_spl                   false
% 0.93/1.00  --abstr_cl_out                          false
% 0.93/1.00  
% 0.93/1.00  ------ Global Options
% 0.93/1.00  
% 0.93/1.00  --schedule                              default
% 0.93/1.00  --add_important_lit                     false
% 0.93/1.00  --prop_solver_per_cl                    1000
% 0.93/1.00  --min_unsat_core                        false
% 0.93/1.00  --soft_assumptions                      false
% 0.93/1.00  --soft_lemma_size                       3
% 0.93/1.00  --prop_impl_unit_size                   0
% 0.93/1.00  --prop_impl_unit                        []
% 0.93/1.00  --share_sel_clauses                     true
% 0.93/1.00  --reset_solvers                         false
% 0.93/1.00  --bc_imp_inh                            [conj_cone]
% 0.93/1.00  --conj_cone_tolerance                   3.
% 0.93/1.00  --extra_neg_conj                        none
% 0.93/1.00  --large_theory_mode                     true
% 0.93/1.00  --prolific_symb_bound                   200
% 0.93/1.00  --lt_threshold                          2000
% 0.93/1.00  --clause_weak_htbl                      true
% 0.93/1.00  --gc_record_bc_elim                     false
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing Options
% 0.93/1.00  
% 0.93/1.00  --preprocessing_flag                    true
% 0.93/1.00  --time_out_prep_mult                    0.1
% 0.93/1.00  --splitting_mode                        input
% 0.93/1.00  --splitting_grd                         true
% 0.93/1.00  --splitting_cvd                         false
% 0.93/1.00  --splitting_cvd_svl                     false
% 0.93/1.00  --splitting_nvd                         32
% 0.93/1.00  --sub_typing                            true
% 0.93/1.00  --prep_gs_sim                           true
% 0.93/1.00  --prep_unflatten                        true
% 0.93/1.00  --prep_res_sim                          true
% 0.93/1.00  --prep_upred                            true
% 0.93/1.00  --prep_sem_filter                       exhaustive
% 0.93/1.00  --prep_sem_filter_out                   false
% 0.93/1.00  --pred_elim                             true
% 0.93/1.00  --res_sim_input                         true
% 0.93/1.00  --eq_ax_congr_red                       true
% 0.93/1.00  --pure_diseq_elim                       true
% 0.93/1.00  --brand_transform                       false
% 0.93/1.00  --non_eq_to_eq                          false
% 0.93/1.00  --prep_def_merge                        true
% 0.93/1.00  --prep_def_merge_prop_impl              false
% 0.93/1.00  --prep_def_merge_mbd                    true
% 0.93/1.00  --prep_def_merge_tr_red                 false
% 0.93/1.00  --prep_def_merge_tr_cl                  false
% 0.93/1.00  --smt_preprocessing                     true
% 0.93/1.00  --smt_ac_axioms                         fast
% 0.93/1.00  --preprocessed_out                      false
% 0.93/1.00  --preprocessed_stats                    false
% 0.93/1.00  
% 0.93/1.00  ------ Abstraction refinement Options
% 0.93/1.00  
% 0.93/1.00  --abstr_ref                             []
% 0.93/1.00  --abstr_ref_prep                        false
% 0.93/1.00  --abstr_ref_until_sat                   false
% 0.93/1.00  --abstr_ref_sig_restrict                funpre
% 0.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.00  --abstr_ref_under                       []
% 0.93/1.00  
% 0.93/1.00  ------ SAT Options
% 0.93/1.00  
% 0.93/1.00  --sat_mode                              false
% 0.93/1.00  --sat_fm_restart_options                ""
% 0.93/1.00  --sat_gr_def                            false
% 0.93/1.00  --sat_epr_types                         true
% 0.93/1.00  --sat_non_cyclic_types                  false
% 0.93/1.00  --sat_finite_models                     false
% 0.93/1.00  --sat_fm_lemmas                         false
% 0.93/1.00  --sat_fm_prep                           false
% 0.93/1.00  --sat_fm_uc_incr                        true
% 0.93/1.00  --sat_out_model                         small
% 0.93/1.00  --sat_out_clauses                       false
% 0.93/1.00  
% 0.93/1.00  ------ QBF Options
% 0.93/1.00  
% 0.93/1.00  --qbf_mode                              false
% 0.93/1.00  --qbf_elim_univ                         false
% 0.93/1.00  --qbf_dom_inst                          none
% 0.93/1.00  --qbf_dom_pre_inst                      false
% 0.93/1.00  --qbf_sk_in                             false
% 0.93/1.00  --qbf_pred_elim                         true
% 0.93/1.00  --qbf_split                             512
% 0.93/1.00  
% 0.93/1.00  ------ BMC1 Options
% 0.93/1.00  
% 0.93/1.00  --bmc1_incremental                      false
% 0.93/1.00  --bmc1_axioms                           reachable_all
% 0.93/1.00  --bmc1_min_bound                        0
% 0.93/1.00  --bmc1_max_bound                        -1
% 0.93/1.00  --bmc1_max_bound_default                -1
% 0.93/1.00  --bmc1_symbol_reachability              true
% 0.93/1.00  --bmc1_property_lemmas                  false
% 0.93/1.00  --bmc1_k_induction                      false
% 0.93/1.00  --bmc1_non_equiv_states                 false
% 0.93/1.00  --bmc1_deadlock                         false
% 0.93/1.00  --bmc1_ucm                              false
% 0.93/1.00  --bmc1_add_unsat_core                   none
% 0.93/1.00  --bmc1_unsat_core_children              false
% 0.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.00  --bmc1_out_stat                         full
% 0.93/1.00  --bmc1_ground_init                      false
% 0.93/1.00  --bmc1_pre_inst_next_state              false
% 0.93/1.00  --bmc1_pre_inst_state                   false
% 0.93/1.00  --bmc1_pre_inst_reach_state             false
% 0.93/1.00  --bmc1_out_unsat_core                   false
% 0.93/1.00  --bmc1_aig_witness_out                  false
% 0.93/1.00  --bmc1_verbose                          false
% 0.93/1.00  --bmc1_dump_clauses_tptp                false
% 0.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.00  --bmc1_dump_file                        -
% 0.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.00  --bmc1_ucm_extend_mode                  1
% 0.93/1.00  --bmc1_ucm_init_mode                    2
% 0.93/1.00  --bmc1_ucm_cone_mode                    none
% 0.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.00  --bmc1_ucm_relax_model                  4
% 0.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.00  --bmc1_ucm_layered_model                none
% 0.93/1.00  --bmc1_ucm_max_lemma_size               10
% 0.93/1.00  
% 0.93/1.00  ------ AIG Options
% 0.93/1.00  
% 0.93/1.00  --aig_mode                              false
% 0.93/1.00  
% 0.93/1.00  ------ Instantiation Options
% 0.93/1.00  
% 0.93/1.00  --instantiation_flag                    true
% 0.93/1.00  --inst_sos_flag                         false
% 0.93/1.00  --inst_sos_phase                        true
% 0.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel_side                     none
% 0.93/1.00  --inst_solver_per_active                1400
% 0.93/1.00  --inst_solver_calls_frac                1.
% 0.93/1.00  --inst_passive_queue_type               priority_queues
% 0.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.00  --inst_passive_queues_freq              [25;2]
% 0.93/1.00  --inst_dismatching                      true
% 0.93/1.00  --inst_eager_unprocessed_to_passive     true
% 0.93/1.00  --inst_prop_sim_given                   true
% 0.93/1.00  --inst_prop_sim_new                     false
% 0.93/1.00  --inst_subs_new                         false
% 0.93/1.00  --inst_eq_res_simp                      false
% 0.93/1.00  --inst_subs_given                       false
% 0.93/1.00  --inst_orphan_elimination               true
% 0.93/1.00  --inst_learning_loop_flag               true
% 0.93/1.00  --inst_learning_start                   3000
% 0.93/1.00  --inst_learning_factor                  2
% 0.93/1.00  --inst_start_prop_sim_after_learn       3
% 0.93/1.00  --inst_sel_renew                        solver
% 0.93/1.00  --inst_lit_activity_flag                true
% 0.93/1.00  --inst_restr_to_given                   false
% 0.93/1.00  --inst_activity_threshold               500
% 0.93/1.00  --inst_out_proof                        true
% 0.93/1.00  
% 0.93/1.00  ------ Resolution Options
% 0.93/1.00  
% 0.93/1.00  --resolution_flag                       false
% 0.93/1.00  --res_lit_sel                           adaptive
% 0.93/1.00  --res_lit_sel_side                      none
% 0.93/1.00  --res_ordering                          kbo
% 0.93/1.00  --res_to_prop_solver                    active
% 0.93/1.00  --res_prop_simpl_new                    false
% 0.93/1.00  --res_prop_simpl_given                  true
% 0.93/1.00  --res_passive_queue_type                priority_queues
% 0.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.00  --res_passive_queues_freq               [15;5]
% 0.93/1.00  --res_forward_subs                      full
% 0.93/1.00  --res_backward_subs                     full
% 0.93/1.00  --res_forward_subs_resolution           true
% 0.93/1.00  --res_backward_subs_resolution          true
% 0.93/1.00  --res_orphan_elimination                true
% 0.93/1.00  --res_time_limit                        2.
% 0.93/1.00  --res_out_proof                         true
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Options
% 0.93/1.00  
% 0.93/1.00  --superposition_flag                    true
% 0.93/1.00  --sup_passive_queue_type                priority_queues
% 0.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.00  --demod_completeness_check              fast
% 0.93/1.00  --demod_use_ground                      true
% 0.93/1.00  --sup_to_prop_solver                    passive
% 0.93/1.00  --sup_prop_simpl_new                    true
% 0.93/1.00  --sup_prop_simpl_given                  true
% 0.93/1.00  --sup_fun_splitting                     false
% 0.93/1.00  --sup_smt_interval                      50000
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Simplification Setup
% 0.93/1.00  
% 0.93/1.00  --sup_indices_passive                   []
% 0.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_full_bw                           [BwDemod]
% 0.93/1.00  --sup_immed_triv                        [TrivRules]
% 0.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_immed_bw_main                     []
% 0.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  
% 0.93/1.00  ------ Combination Options
% 0.93/1.00  
% 0.93/1.00  --comb_res_mult                         3
% 0.93/1.00  --comb_sup_mult                         2
% 0.93/1.00  --comb_inst_mult                        10
% 0.93/1.00  
% 0.93/1.00  ------ Debug Options
% 0.93/1.00  
% 0.93/1.00  --dbg_backtrace                         false
% 0.93/1.00  --dbg_dump_prop_clauses                 false
% 0.93/1.00  --dbg_dump_prop_clauses_file            -
% 0.93/1.00  --dbg_out_stat                          false
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  ------ Proving...
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  % SZS status Theorem for theBenchmark.p
% 0.93/1.00  
% 0.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.93/1.00  
% 0.93/1.00  fof(f1,axiom,(
% 0.93/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f11,plain,(
% 0.93/1.00    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.93/1.00    inference(ennf_transformation,[],[f1])).
% 0.93/1.00  
% 0.93/1.00  fof(f12,plain,(
% 0.93/1.00    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.93/1.00    inference(flattening,[],[f11])).
% 0.93/1.00  
% 0.93/1.00  fof(f31,plain,(
% 0.93/1.00    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f12])).
% 0.93/1.00  
% 0.93/1.00  fof(f5,axiom,(
% 0.93/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f16,plain,(
% 0.93/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.93/1.00    inference(ennf_transformation,[],[f5])).
% 0.93/1.00  
% 0.93/1.00  fof(f17,plain,(
% 0.93/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.93/1.00    inference(flattening,[],[f16])).
% 0.93/1.00  
% 0.93/1.00  fof(f35,plain,(
% 0.93/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f17])).
% 0.93/1.00  
% 0.93/1.00  fof(f9,conjecture,(
% 0.93/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f10,negated_conjecture,(
% 0.93/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.93/1.00    inference(negated_conjecture,[],[f9])).
% 0.93/1.00  
% 0.93/1.00  fof(f23,plain,(
% 0.93/1.00    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.93/1.00    inference(ennf_transformation,[],[f10])).
% 0.93/1.00  
% 0.93/1.00  fof(f24,plain,(
% 0.93/1.00    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.93/1.00    inference(flattening,[],[f23])).
% 0.93/1.00  
% 0.93/1.00  fof(f29,plain,(
% 0.93/1.00    ( ! [X0,X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK2,X1) | r1_tsep_1(X1,sK2)) & m1_pre_topc(X1,sK2) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 0.93/1.00    introduced(choice_axiom,[])).
% 0.93/1.00  
% 0.93/1.00  fof(f28,plain,(
% 0.93/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 0.93/1.00    introduced(choice_axiom,[])).
% 0.93/1.00  
% 0.93/1.00  fof(f27,plain,(
% 0.93/1.00    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.93/1.00    introduced(choice_axiom,[])).
% 0.93/1.00  
% 0.93/1.00  fof(f30,plain,(
% 0.93/1.00    (((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).
% 0.93/1.00  
% 0.93/1.00  fof(f44,plain,(
% 0.93/1.00    ~v2_struct_0(sK1)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f2,axiom,(
% 0.93/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f13,plain,(
% 0.93/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.93/1.00    inference(ennf_transformation,[],[f2])).
% 0.93/1.00  
% 0.93/1.00  fof(f32,plain,(
% 0.93/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f13])).
% 0.93/1.00  
% 0.93/1.00  fof(f7,axiom,(
% 0.93/1.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f19,plain,(
% 0.93/1.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.93/1.00    inference(ennf_transformation,[],[f7])).
% 0.93/1.00  
% 0.93/1.00  fof(f20,plain,(
% 0.93/1.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.93/1.00    inference(flattening,[],[f19])).
% 0.93/1.00  
% 0.93/1.00  fof(f38,plain,(
% 0.93/1.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f20])).
% 0.93/1.00  
% 0.93/1.00  fof(f8,axiom,(
% 0.93/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f21,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.93/1.00    inference(ennf_transformation,[],[f8])).
% 0.93/1.00  
% 0.93/1.00  fof(f22,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.93/1.00    inference(flattening,[],[f21])).
% 0.93/1.00  
% 0.93/1.00  fof(f26,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.93/1.00    inference(nnf_transformation,[],[f22])).
% 0.93/1.00  
% 0.93/1.00  fof(f40,plain,(
% 0.93/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f26])).
% 0.93/1.00  
% 0.93/1.00  fof(f42,plain,(
% 0.93/1.00    v2_pre_topc(sK0)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f43,plain,(
% 0.93/1.00    l1_pre_topc(sK0)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f49,plain,(
% 0.93/1.00    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f45,plain,(
% 0.93/1.00    m1_pre_topc(sK1,sK0)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f47,plain,(
% 0.93/1.00    m1_pre_topc(sK2,sK0)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  fof(f3,axiom,(
% 0.93/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f14,plain,(
% 0.93/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.93/1.00    inference(ennf_transformation,[],[f3])).
% 0.93/1.00  
% 0.93/1.00  fof(f33,plain,(
% 0.93/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f14])).
% 0.93/1.00  
% 0.93/1.00  fof(f4,axiom,(
% 0.93/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f15,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.93/1.00    inference(ennf_transformation,[],[f4])).
% 0.93/1.00  
% 0.93/1.00  fof(f34,plain,(
% 0.93/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f15])).
% 0.93/1.00  
% 0.93/1.00  fof(f6,axiom,(
% 0.93/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.00  
% 0.93/1.00  fof(f18,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.93/1.00    inference(ennf_transformation,[],[f6])).
% 0.93/1.00  
% 0.93/1.00  fof(f25,plain,(
% 0.93/1.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.93/1.00    inference(nnf_transformation,[],[f18])).
% 0.93/1.00  
% 0.93/1.00  fof(f36,plain,(
% 0.93/1.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.93/1.00    inference(cnf_transformation,[],[f25])).
% 0.93/1.00  
% 0.93/1.00  fof(f48,plain,(
% 0.93/1.00    m1_pre_topc(sK1,sK2)),
% 0.93/1.00    inference(cnf_transformation,[],[f30])).
% 0.93/1.00  
% 0.93/1.00  cnf(c_832,plain,
% 0.93/1.00      ( ~ r1_xboole_0(X0_43,X1_43)
% 0.93/1.00      | r1_xboole_0(X2_43,X3_43)
% 0.93/1.00      | X2_43 != X0_43
% 0.93/1.00      | X3_43 != X1_43 ),
% 0.93/1.00      theory(equality) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1276,plain,
% 0.93/1.00      ( r1_xboole_0(X0_43,X1_43)
% 0.93/1.00      | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | X0_43 != u1_struct_0(sK1)
% 0.93/1.00      | X1_43 != u1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_832]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1532,plain,
% 0.93/1.00      ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | r1_xboole_0(k2_struct_0(sK1),X0_43)
% 0.93/1.00      | X0_43 != u1_struct_0(sK2)
% 0.93/1.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1276]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1621,plain,
% 0.93/1.00      ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 0.93/1.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1532]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_0,plain,
% 0.93/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_4,plain,
% 0.93/1.00      ( v2_struct_0(X0)
% 0.93/1.00      | ~ l1_struct_0(X0)
% 0.93/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 0.93/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_15,negated_conjecture,
% 0.93/1.00      ( ~ v2_struct_0(sK1) ),
% 0.93/1.00      inference(cnf_transformation,[],[f44]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_231,plain,
% 0.93/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 0.93/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_232,plain,
% 0.93/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.93/1.00      inference(unflattening,[status(thm)],[c_231]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_287,plain,
% 0.93/1.00      ( ~ r1_tarski(X0,X1)
% 0.93/1.00      | ~ r1_xboole_0(X0,X1)
% 0.93/1.00      | ~ l1_struct_0(sK1)
% 0.93/1.00      | k2_struct_0(sK1) != X0 ),
% 0.93/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_232]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_288,plain,
% 0.93/1.00      ( ~ r1_tarski(k2_struct_0(sK1),X0)
% 0.93/1.00      | ~ r1_xboole_0(k2_struct_0(sK1),X0)
% 0.93/1.00      | ~ l1_struct_0(sK1) ),
% 0.93/1.00      inference(unflattening,[status(thm)],[c_287]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_815,plain,
% 0.93/1.00      ( ~ r1_tarski(k2_struct_0(sK1),X0_43)
% 0.93/1.00      | ~ r1_xboole_0(k2_struct_0(sK1),X0_43)
% 0.93/1.00      | ~ l1_struct_0(sK1) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_288]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1612,plain,
% 0.93/1.00      ( ~ r1_tarski(k2_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | ~ r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | ~ l1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_815]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_830,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1558,plain,
% 0.93/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_830]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_833,plain,
% 0.93/1.00      ( ~ r1_tarski(X0_43,X1_43)
% 0.93/1.00      | r1_tarski(X2_43,X3_43)
% 0.93/1.00      | X2_43 != X0_43
% 0.93/1.00      | X3_43 != X1_43 ),
% 0.93/1.00      theory(equality) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1286,plain,
% 0.93/1.00      ( r1_tarski(X0_43,X1_43)
% 0.93/1.00      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_42))
% 0.93/1.00      | X1_43 != u1_struct_0(X0_42)
% 0.93/1.00      | X0_43 != u1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_833]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1368,plain,
% 0.93/1.00      ( r1_tarski(X0_43,X1_43)
% 0.93/1.00      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | X0_43 != u1_struct_0(sK1)
% 0.93/1.00      | X1_43 != u1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1286]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1531,plain,
% 0.93/1.00      ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | r1_tarski(k2_struct_0(sK1),X0_43)
% 0.93/1.00      | X0_43 != u1_struct_0(sK2)
% 0.93/1.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1368]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1557,plain,
% 0.93/1.00      ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | r1_tarski(k2_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 0.93/1.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1487,plain,
% 0.93/1.00      ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_830]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_831,plain,
% 0.93/1.00      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 0.93/1.00      theory(equality) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1396,plain,
% 0.93/1.00      ( X0_43 != X1_43
% 0.93/1.00      | X0_43 = u1_struct_0(sK1)
% 0.93/1.00      | u1_struct_0(sK1) != X1_43 ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_831]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1461,plain,
% 0.93/1.00      ( X0_43 = u1_struct_0(sK1)
% 0.93/1.00      | X0_43 != k2_struct_0(sK1)
% 0.93/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1396]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1486,plain,
% 0.93/1.00      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 0.93/1.00      | k2_struct_0(sK1) = u1_struct_0(sK1)
% 0.93/1.00      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1461]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1,plain,
% 0.93/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_828,plain,
% 0.93/1.00      ( ~ l1_struct_0(X0_42) | u1_struct_0(X0_42) = k2_struct_0(X0_42) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1462,plain,
% 0.93/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_828]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_7,plain,
% 0.93/1.00      ( ~ r1_tsep_1(X0,X1)
% 0.93/1.00      | r1_tsep_1(X1,X0)
% 0.93/1.00      | ~ l1_struct_0(X0)
% 0.93/1.00      | ~ l1_struct_0(X1) ),
% 0.93/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_823,plain,
% 0.93/1.00      ( ~ r1_tsep_1(X0_42,X1_42)
% 0.93/1.00      | r1_tsep_1(X1_42,X0_42)
% 0.93/1.00      | ~ l1_struct_0(X0_42)
% 0.93/1.00      | ~ l1_struct_0(X1_42) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1344,plain,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2)
% 0.93/1.00      | ~ r1_tsep_1(sK2,sK1)
% 0.93/1.00      | ~ l1_struct_0(sK1)
% 0.93/1.00      | ~ l1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_823]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_8,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.93/1.00      | ~ m1_pre_topc(X0,X2)
% 0.93/1.00      | ~ m1_pre_topc(X2,X1)
% 0.93/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 0.93/1.00      | ~ v2_pre_topc(X1)
% 0.93/1.00      | ~ l1_pre_topc(X1) ),
% 0.93/1.00      inference(cnf_transformation,[],[f40]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_17,negated_conjecture,
% 0.93/1.00      ( v2_pre_topc(sK0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f42]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_333,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.93/1.00      | ~ m1_pre_topc(X0,X2)
% 0.93/1.00      | ~ m1_pre_topc(X2,X1)
% 0.93/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 0.93/1.00      | ~ l1_pre_topc(X1)
% 0.93/1.00      | sK0 != X1 ),
% 0.93/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_334,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.93/1.00      | ~ m1_pre_topc(X1,sK0)
% 0.93/1.00      | ~ m1_pre_topc(X0,sK0)
% 0.93/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 0.93/1.00      | ~ l1_pre_topc(sK0) ),
% 0.93/1.00      inference(unflattening,[status(thm)],[c_333]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_16,negated_conjecture,
% 0.93/1.00      ( l1_pre_topc(sK0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f43]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_338,plain,
% 0.93/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 0.93/1.00      | ~ m1_pre_topc(X0,sK0)
% 0.93/1.00      | ~ m1_pre_topc(X1,sK0)
% 0.93/1.00      | ~ m1_pre_topc(X0,X1) ),
% 0.93/1.00      inference(global_propositional_subsumption,
% 0.93/1.00                [status(thm)],
% 0.93/1.00                [c_334,c_16]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_339,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.93/1.00      | ~ m1_pre_topc(X0,sK0)
% 0.93/1.00      | ~ m1_pre_topc(X1,sK0)
% 0.93/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 0.93/1.00      inference(renaming,[status(thm)],[c_338]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_813,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0_42,X1_42)
% 0.93/1.00      | ~ m1_pre_topc(X0_42,sK0)
% 0.93/1.00      | ~ m1_pre_topc(X1_42,sK0)
% 0.93/1.00      | r1_tarski(u1_struct_0(X0_42),u1_struct_0(X1_42)) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_339]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1241,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0_42,sK0)
% 0.93/1.00      | ~ m1_pre_topc(sK1,X0_42)
% 0.93/1.00      | ~ m1_pre_topc(sK1,sK0)
% 0.93/1.00      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_42)) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_813]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1325,plain,
% 0.93/1.00      ( ~ m1_pre_topc(sK1,sK0)
% 0.93/1.00      | ~ m1_pre_topc(sK1,sK2)
% 0.93/1.00      | ~ m1_pre_topc(sK2,sK0)
% 0.93/1.00      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1241]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_10,negated_conjecture,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2) | r1_tsep_1(sK2,sK1) ),
% 0.93/1.00      inference(cnf_transformation,[],[f49]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_822,negated_conjecture,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2) | r1_tsep_1(sK2,sK1) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1110,plain,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2) = iProver_top
% 0.93/1.00      | r1_tsep_1(sK2,sK1) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_21,plain,
% 0.93/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_14,negated_conjecture,
% 0.93/1.00      ( m1_pre_topc(sK1,sK0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f45]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_23,plain,
% 0.93/1.00      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_12,negated_conjecture,
% 0.93/1.00      ( m1_pre_topc(sK2,sK0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f47]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_25,plain,
% 0.93/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_27,plain,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2) = iProver_top
% 0.93/1.00      | r1_tsep_1(sK2,sK1) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_2,plain,
% 0.93/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_827,plain,
% 0.93/1.00      ( ~ l1_pre_topc(X0_42) | l1_struct_0(X0_42) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1256,plain,
% 0.93/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_827]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1257,plain,
% 0.93/1.00      ( l1_pre_topc(sK2) != iProver_top
% 0.93/1.00      | l1_struct_0(sK2) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1259,plain,
% 0.93/1.00      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_827]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1260,plain,
% 0.93/1.00      ( l1_pre_topc(sK1) != iProver_top
% 0.93/1.00      | l1_struct_0(sK1) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1262,plain,
% 0.93/1.00      ( ~ r1_tsep_1(sK1,sK2)
% 0.93/1.00      | r1_tsep_1(sK2,sK1)
% 0.93/1.00      | ~ l1_struct_0(sK1)
% 0.93/1.00      | ~ l1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_823]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1263,plain,
% 0.93/1.00      ( r1_tsep_1(sK1,sK2) != iProver_top
% 0.93/1.00      | r1_tsep_1(sK2,sK1) = iProver_top
% 0.93/1.00      | l1_struct_0(sK1) != iProver_top
% 0.93/1.00      | l1_struct_0(sK2) != iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_3,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 0.93/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_826,plain,
% 0.93/1.00      ( ~ m1_pre_topc(X0_42,X1_42)
% 0.93/1.00      | ~ l1_pre_topc(X1_42)
% 0.93/1.00      | l1_pre_topc(X0_42) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1292,plain,
% 0.93/1.00      ( ~ m1_pre_topc(sK2,X0_42)
% 0.93/1.00      | ~ l1_pre_topc(X0_42)
% 0.93/1.00      | l1_pre_topc(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_826]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1293,plain,
% 0.93/1.00      ( m1_pre_topc(sK2,X0_42) != iProver_top
% 0.93/1.00      | l1_pre_topc(X0_42) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1295,plain,
% 0.93/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK0) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1293]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1297,plain,
% 0.93/1.00      ( ~ m1_pre_topc(sK1,X0_42)
% 0.93/1.00      | ~ l1_pre_topc(X0_42)
% 0.93/1.00      | l1_pre_topc(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_826]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1298,plain,
% 0.93/1.00      ( m1_pre_topc(sK1,X0_42) != iProver_top
% 0.93/1.00      | l1_pre_topc(X0_42) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK1) = iProver_top ),
% 0.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1300,plain,
% 0.93/1.00      ( m1_pre_topc(sK1,sK0) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK0) != iProver_top
% 0.93/1.00      | l1_pre_topc(sK1) = iProver_top ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1298]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1304,plain,
% 0.93/1.00      ( r1_tsep_1(sK2,sK1) = iProver_top ),
% 0.93/1.00      inference(global_propositional_subsumption,
% 0.93/1.00                [status(thm)],
% 0.93/1.00                [c_1110,c_21,c_23,c_25,c_27,c_1257,c_1260,c_1263,c_1295,
% 0.93/1.00                 c_1300]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1306,plain,
% 0.93/1.00      ( r1_tsep_1(sK2,sK1) ),
% 0.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1304]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1299,plain,
% 0.93/1.00      ( ~ m1_pre_topc(sK1,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK1) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1297]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1294,plain,
% 0.93/1.00      ( ~ m1_pre_topc(sK2,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_1292]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_6,plain,
% 0.93/1.00      ( ~ r1_tsep_1(X0,X1)
% 0.93/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 0.93/1.00      | ~ l1_struct_0(X0)
% 0.93/1.00      | ~ l1_struct_0(X1) ),
% 0.93/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_824,plain,
% 0.93/1.00      ( ~ r1_tsep_1(X0_42,X1_42)
% 0.93/1.00      | r1_xboole_0(u1_struct_0(X0_42),u1_struct_0(X1_42))
% 0.93/1.00      | ~ l1_struct_0(X0_42)
% 0.93/1.00      | ~ l1_struct_0(X1_42) ),
% 0.93/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_1265,plain,
% 0.93/1.00      ( ~ r1_tsep_1(sK1,sK2)
% 0.93/1.00      | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 0.93/1.00      | ~ l1_struct_0(sK1)
% 0.93/1.00      | ~ l1_struct_0(sK2) ),
% 0.93/1.00      inference(instantiation,[status(thm)],[c_824]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(c_11,negated_conjecture,
% 0.93/1.00      ( m1_pre_topc(sK1,sK2) ),
% 0.93/1.00      inference(cnf_transformation,[],[f48]) ).
% 0.93/1.00  
% 0.93/1.00  cnf(contradiction,plain,
% 0.93/1.00      ( $false ),
% 0.93/1.00      inference(minisat,
% 0.93/1.00                [status(thm)],
% 0.93/1.00                [c_1621,c_1612,c_1558,c_1557,c_1487,c_1486,c_1462,c_1344,
% 0.93/1.00                 c_1325,c_1306,c_1299,c_1294,c_1265,c_1259,c_1256,c_11,
% 0.93/1.00                 c_12,c_14,c_16]) ).
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.93/1.00  
% 0.93/1.00  ------                               Statistics
% 0.93/1.00  
% 0.93/1.00  ------ General
% 0.93/1.00  
% 0.93/1.00  abstr_ref_over_cycles:                  0
% 0.93/1.00  abstr_ref_under_cycles:                 0
% 0.93/1.00  gc_basic_clause_elim:                   0
% 0.93/1.00  forced_gc_time:                         0
% 0.93/1.00  parsing_time:                           0.008
% 0.93/1.00  unif_index_cands_time:                  0.
% 0.93/1.00  unif_index_add_time:                    0.
% 0.93/1.00  orderings_time:                         0.
% 0.93/1.00  out_proof_time:                         0.012
% 0.93/1.00  total_time:                             0.074
% 0.93/1.00  num_of_symbols:                         44
% 0.93/1.00  num_of_terms:                           902
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing
% 0.93/1.00  
% 0.93/1.00  num_of_splits:                          0
% 0.93/1.00  num_of_split_atoms:                     0
% 0.93/1.00  num_of_reused_defs:                     0
% 0.93/1.00  num_eq_ax_congr_red:                    12
% 0.93/1.00  num_of_sem_filtered_clauses:            1
% 0.93/1.00  num_of_subtypes:                        2
% 0.93/1.00  monotx_restored_types:                  0
% 0.93/1.00  sat_num_of_epr_types:                   0
% 0.93/1.00  sat_num_of_non_cyclic_types:            0
% 0.93/1.00  sat_guarded_non_collapsed_types:        0
% 0.93/1.00  num_pure_diseq_elim:                    0
% 0.93/1.00  simp_replaced_by:                       0
% 0.93/1.00  res_preprocessed:                       76
% 0.93/1.00  prep_upred:                             0
% 0.93/1.00  prep_unflattend:                        21
% 0.93/1.00  smt_new_axioms:                         0
% 0.93/1.00  pred_elim_cands:                        6
% 0.93/1.00  pred_elim:                              3
% 0.93/1.00  pred_elim_cl:                           3
% 0.93/1.00  pred_elim_cycles:                       8
% 0.93/1.00  merged_defs:                            0
% 0.93/1.00  merged_defs_ncl:                        0
% 0.93/1.00  bin_hyper_res:                          0
% 0.93/1.00  prep_cycles:                            4
% 0.93/1.00  pred_elim_time:                         0.007
% 0.93/1.00  splitting_time:                         0.
% 0.93/1.00  sem_filter_time:                        0.
% 0.93/1.00  monotx_time:                            0.
% 0.93/1.00  subtype_inf_time:                       0.
% 0.93/1.00  
% 0.93/1.00  ------ Problem properties
% 0.93/1.00  
% 0.93/1.00  clauses:                                16
% 0.93/1.00  conjectures:                            5
% 0.93/1.00  epr:                                    8
% 0.93/1.00  horn:                                   15
% 0.93/1.00  ground:                                 5
% 0.93/1.00  unary:                                  4
% 0.93/1.00  binary:                                 4
% 0.93/1.00  lits:                                   41
% 0.93/1.00  lits_eq:                                1
% 0.93/1.00  fd_pure:                                0
% 0.93/1.00  fd_pseudo:                              0
% 0.93/1.00  fd_cond:                                0
% 0.93/1.00  fd_pseudo_cond:                         0
% 0.93/1.00  ac_symbols:                             0
% 0.93/1.00  
% 0.93/1.00  ------ Propositional Solver
% 0.93/1.00  
% 0.93/1.00  prop_solver_calls:                      28
% 0.93/1.00  prop_fast_solver_calls:                 542
% 0.93/1.00  smt_solver_calls:                       0
% 0.93/1.00  smt_fast_solver_calls:                  0
% 0.93/1.00  prop_num_of_clauses:                    325
% 0.93/1.00  prop_preprocess_simplified:             2189
% 0.93/1.00  prop_fo_subsumed:                       9
% 0.93/1.00  prop_solver_time:                       0.
% 0.93/1.00  smt_solver_time:                        0.
% 0.93/1.00  smt_fast_solver_time:                   0.
% 0.93/1.00  prop_fast_solver_time:                  0.
% 0.93/1.00  prop_unsat_core_time:                   0.
% 0.93/1.00  
% 0.93/1.00  ------ QBF
% 0.93/1.00  
% 0.93/1.00  qbf_q_res:                              0
% 0.93/1.00  qbf_num_tautologies:                    0
% 0.93/1.00  qbf_prep_cycles:                        0
% 0.93/1.00  
% 0.93/1.00  ------ BMC1
% 0.93/1.00  
% 0.93/1.00  bmc1_current_bound:                     -1
% 0.93/1.00  bmc1_last_solved_bound:                 -1
% 0.93/1.00  bmc1_unsat_core_size:                   -1
% 0.93/1.00  bmc1_unsat_core_parents_size:           -1
% 0.93/1.00  bmc1_merge_next_fun:                    0
% 0.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.93/1.00  
% 0.93/1.00  ------ Instantiation
% 0.93/1.00  
% 0.93/1.00  inst_num_of_clauses:                    82
% 0.93/1.00  inst_num_in_passive:                    6
% 0.93/1.00  inst_num_in_active:                     73
% 0.93/1.00  inst_num_in_unprocessed:                2
% 0.93/1.00  inst_num_of_loops:                      97
% 0.93/1.00  inst_num_of_learning_restarts:          0
% 0.93/1.00  inst_num_moves_active_passive:          15
% 0.93/1.00  inst_lit_activity:                      0
% 0.93/1.00  inst_lit_activity_moves:                0
% 0.93/1.00  inst_num_tautologies:                   0
% 0.93/1.00  inst_num_prop_implied:                  0
% 0.93/1.00  inst_num_existing_simplified:           0
% 0.93/1.00  inst_num_eq_res_simplified:             0
% 0.93/1.00  inst_num_child_elim:                    0
% 0.93/1.00  inst_num_of_dismatching_blockings:      2
% 0.93/1.00  inst_num_of_non_proper_insts:           75
% 0.93/1.00  inst_num_of_duplicates:                 0
% 0.93/1.00  inst_inst_num_from_inst_to_res:         0
% 0.93/1.00  inst_dismatching_checking_time:         0.
% 0.93/1.00  
% 0.93/1.00  ------ Resolution
% 0.93/1.00  
% 0.93/1.00  res_num_of_clauses:                     0
% 0.93/1.00  res_num_in_passive:                     0
% 0.93/1.00  res_num_in_active:                      0
% 0.93/1.00  res_num_of_loops:                       80
% 0.93/1.00  res_forward_subset_subsumed:            13
% 0.93/1.00  res_backward_subset_subsumed:           0
% 0.93/1.00  res_forward_subsumed:                   0
% 0.93/1.00  res_backward_subsumed:                  0
% 0.93/1.00  res_forward_subsumption_resolution:     0
% 0.93/1.00  res_backward_subsumption_resolution:    0
% 0.93/1.00  res_clause_to_clause_subsumption:       31
% 0.93/1.00  res_orphan_elimination:                 0
% 0.93/1.00  res_tautology_del:                      18
% 0.93/1.00  res_num_eq_res_simplified:              0
% 0.93/1.00  res_num_sel_changes:                    0
% 0.93/1.00  res_moves_from_active_to_pass:          0
% 0.93/1.00  
% 0.93/1.00  ------ Superposition
% 0.93/1.00  
% 0.93/1.00  sup_time_total:                         0.
% 0.93/1.00  sup_time_generating:                    0.
% 0.93/1.00  sup_time_sim_full:                      0.
% 0.93/1.00  sup_time_sim_immed:                     0.
% 0.93/1.00  
% 0.93/1.00  sup_num_of_clauses:                     25
% 0.93/1.00  sup_num_in_active:                      18
% 0.93/1.00  sup_num_in_passive:                     7
% 0.93/1.00  sup_num_of_loops:                       18
% 0.93/1.00  sup_fw_superposition:                   5
% 0.93/1.00  sup_bw_superposition:                   6
% 0.93/1.00  sup_immediate_simplified:               1
% 0.93/1.00  sup_given_eliminated:                   0
% 0.93/1.00  comparisons_done:                       0
% 0.93/1.00  comparisons_avoided:                    0
% 0.93/1.00  
% 0.93/1.00  ------ Simplifications
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  sim_fw_subset_subsumed:                 1
% 0.93/1.00  sim_bw_subset_subsumed:                 0
% 0.93/1.00  sim_fw_subsumed:                        0
% 0.93/1.00  sim_bw_subsumed:                        0
% 0.93/1.00  sim_fw_subsumption_res:                 0
% 0.93/1.00  sim_bw_subsumption_res:                 0
% 0.93/1.00  sim_tautology_del:                      0
% 0.93/1.00  sim_eq_tautology_del:                   0
% 0.93/1.00  sim_eq_res_simp:                        0
% 0.93/1.00  sim_fw_demodulated:                     0
% 0.93/1.00  sim_bw_demodulated:                     0
% 0.93/1.00  sim_light_normalised:                   0
% 0.93/1.00  sim_joinable_taut:                      0
% 0.93/1.00  sim_joinable_simp:                      0
% 0.93/1.00  sim_ac_normalised:                      0
% 0.93/1.00  sim_smt_subsumption:                    0
% 0.93/1.00  
%------------------------------------------------------------------------------
