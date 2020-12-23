%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1720+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:16 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 382 expanded)
%              Number of clauses        :   77 ( 101 expanded)
%              Number of leaves         :    9 ( 129 expanded)
%              Depth                    :   25
%              Number of atoms          :  575 (3685 expanded)
%              Number of equality atoms :   92 (  97 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
          & m1_pre_topc(X3,X2)
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2)
        & m1_pre_topc(sK3,X2)
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2)
            & m1_pre_topc(X3,sK2)
            & m1_pre_topc(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22,f21,f20,f19])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_725,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1061,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_721,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1065,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(k1_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_113,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_4,c_3,c_2])).

cnf(c_114,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_113])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_322,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_114,c_17])).

cnf(c_323,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,X1,X0)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_327,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | u1_struct_0(k1_tsep_1(sK0,X1,X0)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_19])).

cnf(c_328,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(sK0,X1,X0)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_716,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | v2_struct_0(X0_41)
    | v2_struct_0(X1_41)
    | u1_struct_0(k1_tsep_1(sK0,X1_41,X0_41)) = k2_xboole_0(u1_struct_0(X1_41),u1_struct_0(X0_41)) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_1070,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0_41,X1_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | m1_pre_topc(X1_41,sK0) != iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2515,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_1070])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3808,plain,
    ( v2_struct_0(X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_23])).

cnf(c_3809,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_3808])).

cnf(c_3814,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_3809])).

cnf(c_12,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3835,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3814,c_27])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_729,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X1_42)
    | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1057,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X1_42) != iProver_top
    | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_3837,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),X0_42) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0_42) != iProver_top
    | r1_tarski(u1_struct_0(sK1),X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_1057])).

cnf(c_6,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_212,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_213,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_215,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_17])).

cnf(c_216,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_718,plain,
    ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0) ),
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_1068,plain,
    ( r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) != iProver_top
    | m1_pre_topc(X0_41,X1_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(X1_41,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_4056,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3837,c_1068])).

cnf(c_24,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_28,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_397,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_398,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_402,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | m1_pre_topc(k1_tsep_1(sK0,X1,X0),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_19])).

cnf(c_403,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_713,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X1_41,X0_41),sK0)
    | v2_struct_0(X0_41)
    | v2_struct_0(X1_41) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_1129,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_41,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_41)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1234,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1235,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_4423,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4056,c_23,c_24,c_27,c_28,c_1235])).

cnf(c_4424,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_4423])).

cnf(c_8,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_728,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1058,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_4429,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4424,c_1058])).

cnf(c_5,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_232,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_233,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_237,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_17])).

cnf(c_238,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_237])).

cnf(c_717,plain,
    ( r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | ~ m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_1189,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41))
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(sK1,X0_41)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1367,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_1368,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_1179,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41))
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(sK3,X0_41)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1347,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_1348,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1347])).

cnf(c_9,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_30,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4429,c_1368,c_1348,c_30,c_29,c_28,c_26,c_24])).


%------------------------------------------------------------------------------
