%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:09 EST 2020

% Result     : Theorem 39.51s
% Output     : CNFRefutation 39.51s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 590 expanded)
%              Number of clauses        :  117 ( 174 expanded)
%              Number of leaves         :   19 ( 192 expanded)
%              Depth                    :   17
%              Number of atoms          :  788 (5314 expanded)
%              Number of equality atoms :  141 ( 180 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f32,f31,f30,f29])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_389,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1240,plain,
    ( X0_44 != X1_44
    | X0_44 = u1_struct_0(X0_43)
    | u1_struct_0(X0_43) != X1_44 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_1347,plain,
    ( X0_44 != u1_struct_0(X0_43)
    | X0_44 = u1_struct_0(X1_43)
    | u1_struct_0(X1_43) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_1500,plain,
    ( u1_struct_0(X0_43) != u1_struct_0(X1_43)
    | u1_struct_0(X2_43) != u1_struct_0(X1_43)
    | u1_struct_0(X0_43) = u1_struct_0(X2_43) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_3190,plain,
    ( u1_struct_0(X0_43) != u1_struct_0(X1_43)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X1_43)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_5974,plain,
    ( u1_struct_0(X0_43) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_8017,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_5974])).

cnf(c_132877,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_8017])).

cnf(c_399,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_1158,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | X0_44 != u1_struct_0(X0_43)
    | X1_44 != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1242,plain,
    ( r1_tarski(X0_44,u1_struct_0(X0_43))
    | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | X0_44 != u1_struct_0(X1_43)
    | u1_struct_0(X0_43) != u1_struct_0(X2_43) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_1552,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X3_43))
    | u1_struct_0(X2_43) != u1_struct_0(X0_43)
    | u1_struct_0(X3_43) != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_2412,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43)
    | u1_struct_0(sK2) != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_3191,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(X1_43))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_4350,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3191])).

cnf(c_68218,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_13,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_374,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ v2_pre_topc(X2_43)
    | ~ l1_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3214,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(sK2,X1_43)
    | ~ v2_pre_topc(X1_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_4393,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0_43,X1_43)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,X0_43,X1_43),X2_43)
    | ~ m1_pre_topc(k1_tsep_1(sK2,X0_43,X1_43),sK2)
    | ~ m1_pre_topc(sK2,X2_43)
    | ~ v2_pre_topc(X2_43)
    | ~ l1_pre_topc(X2_43) ),
    inference(instantiation,[status(thm)],[c_3214])).

cnf(c_8636,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_43)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_4393])).

cnf(c_11685,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
    inference(instantiation,[status(thm)],[c_8636])).

cnf(c_32483,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_11685])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_376,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_398,plain,
    ( ~ v2_pre_topc(X0_43)
    | v2_pre_topc(X1_43)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_3996,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ v2_pre_topc(X1_43)
    | ~ v2_pre_topc(k1_tsep_1(X1_43,X0_43,X0_43))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(resolution,[status(thm)],[c_376,c_398])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_377,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43))
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9857,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(resolution,[status(thm)],[c_3996,c_377])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_367,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_11843,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_9857,c_367])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_191,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_192,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_360,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_8123,plain,
    ( m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(X0_43,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_10050,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8123])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_369,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_833,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_365,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_837,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6,c_5])).

cnf(c_225,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_359,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_843,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_4446,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_843])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7131,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4446,c_27,c_29,c_30])).

cnf(c_7132,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_7131])).

cnf(c_7140,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_7132])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_371,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_831,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_370,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_832,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_4443,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_843])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_383,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1190,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_383,c_367])).

cnf(c_1191,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_5461,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4443,c_29,c_30,c_32,c_1191])).

cnf(c_5462,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5461])).

cnf(c_5470,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_5462])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5628,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5470,c_34])).

cnf(c_7189,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7140,c_5628])).

cnf(c_3629,plain,
    ( m1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_5401,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3629])).

cnf(c_380,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4767,plain,
    ( m1_pre_topc(k1_tsep_1(X0_43,sK2,sK2),X0_43)
    | ~ m1_pre_topc(sK2,X0_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_4769,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_4767])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_375,plain,
    ( m1_pre_topc(X0_43,X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4386,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_392,plain,
    ( u1_struct_0(X0_43) = u1_struct_0(X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_3186,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43)
    | k1_tsep_1(sK0,sK1,sK3) != X0_43 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_4150,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3186])).

cnf(c_3449,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_3437,plain,
    ( ~ m1_pre_topc(k1_tsep_1(X0_43,sK2,sK2),X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(k1_tsep_1(X0_43,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_3439,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(c_390,plain,
    ( ~ l1_pre_topc(X0_43)
    | l1_pre_topc(X1_43)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1571,plain,
    ( ~ l1_pre_topc(X0_43)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_2160,plain,
    ( ~ l1_pre_topc(k1_tsep_1(X0_43,sK2,sK2))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(X0_43,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_2163,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_2133,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_835,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_826,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_1705,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_826])).

cnf(c_385,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1407,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_1313,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_1206,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_14,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_373,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | m1_pre_topc(X0_43,X1_43)
    | ~ v2_pre_topc(X2_43)
    | ~ l1_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1130,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1132,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_15,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132877,c_68218,c_32483,c_11843,c_10050,c_7189,c_5401,c_4769,c_4386,c_4150,c_3449,c_3439,c_2163,c_2133,c_1705,c_1407,c_1313,c_1206,c_1190,c_1132,c_15,c_16,c_17,c_18,c_34,c_19,c_20,c_32,c_21,c_22,c_23,c_29,c_24,c_28,c_25,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.51/5.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.51/5.51  
% 39.51/5.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.51/5.51  
% 39.51/5.51  ------  iProver source info
% 39.51/5.51  
% 39.51/5.51  git: date: 2020-06-30 10:37:57 +0100
% 39.51/5.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.51/5.51  git: non_committed_changes: false
% 39.51/5.51  git: last_make_outside_of_git: false
% 39.51/5.51  
% 39.51/5.51  ------ 
% 39.51/5.51  ------ Parsing...
% 39.51/5.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.51/5.51  
% 39.51/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.51/5.51  
% 39.51/5.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.51/5.51  
% 39.51/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.51/5.51  ------ Proving...
% 39.51/5.51  ------ Problem Properties 
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  clauses                                 25
% 39.51/5.51  conjectures                             12
% 39.51/5.51  EPR                                     13
% 39.51/5.51  Horn                                    18
% 39.51/5.51  unary                                   12
% 39.51/5.51  binary                                  1
% 39.51/5.51  lits                                    89
% 39.51/5.51  lits eq                                 4
% 39.51/5.51  fd_pure                                 0
% 39.51/5.51  fd_pseudo                               0
% 39.51/5.51  fd_cond                                 0
% 39.51/5.51  fd_pseudo_cond                          1
% 39.51/5.51  AC symbols                              0
% 39.51/5.51  
% 39.51/5.51  ------ Input Options Time Limit: Unbounded
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  ------ 
% 39.51/5.51  Current options:
% 39.51/5.51  ------ 
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  ------ Proving...
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  % SZS status Theorem for theBenchmark.p
% 39.51/5.51  
% 39.51/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.51/5.51  
% 39.51/5.51  fof(f8,axiom,(
% 39.51/5.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f22,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f8])).
% 39.51/5.51  
% 39.51/5.51  fof(f23,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.51/5.51    inference(flattening,[],[f22])).
% 39.51/5.51  
% 39.51/5.51  fof(f28,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.51/5.51    inference(nnf_transformation,[],[f23])).
% 39.51/5.51  
% 39.51/5.51  fof(f48,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f28])).
% 39.51/5.51  
% 39.51/5.51  fof(f6,axiom,(
% 39.51/5.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f19,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f6])).
% 39.51/5.51  
% 39.51/5.51  fof(f20,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.51/5.51    inference(flattening,[],[f19])).
% 39.51/5.51  
% 39.51/5.51  fof(f45,plain,(
% 39.51/5.51    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f20])).
% 39.51/5.51  
% 39.51/5.51  fof(f5,axiom,(
% 39.51/5.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f17,plain,(
% 39.51/5.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f5])).
% 39.51/5.51  
% 39.51/5.51  fof(f18,plain,(
% 39.51/5.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.51/5.51    inference(flattening,[],[f17])).
% 39.51/5.51  
% 39.51/5.51  fof(f44,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f18])).
% 39.51/5.51  
% 39.51/5.51  fof(f9,conjecture,(
% 39.51/5.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f10,negated_conjecture,(
% 39.51/5.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 39.51/5.51    inference(negated_conjecture,[],[f9])).
% 39.51/5.51  
% 39.51/5.51  fof(f24,plain,(
% 39.51/5.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f10])).
% 39.51/5.51  
% 39.51/5.51  fof(f25,plain,(
% 39.51/5.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 39.51/5.51    inference(flattening,[],[f24])).
% 39.51/5.51  
% 39.51/5.51  fof(f32,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 39.51/5.51    introduced(choice_axiom,[])).
% 39.51/5.51  
% 39.51/5.51  fof(f31,plain,(
% 39.51/5.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 39.51/5.51    introduced(choice_axiom,[])).
% 39.51/5.51  
% 39.51/5.51  fof(f30,plain,(
% 39.51/5.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 39.51/5.51    introduced(choice_axiom,[])).
% 39.51/5.51  
% 39.51/5.51  fof(f29,plain,(
% 39.51/5.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 39.51/5.51    introduced(choice_axiom,[])).
% 39.51/5.51  
% 39.51/5.51  fof(f33,plain,(
% 39.51/5.51    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 39.51/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f32,f31,f30,f29])).
% 39.51/5.51  
% 39.51/5.51  fof(f55,plain,(
% 39.51/5.51    m1_pre_topc(sK2,sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f2,axiom,(
% 39.51/5.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f12,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 39.51/5.51    inference(ennf_transformation,[],[f2])).
% 39.51/5.51  
% 39.51/5.51  fof(f26,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 39.51/5.51    inference(nnf_transformation,[],[f12])).
% 39.51/5.51  
% 39.51/5.51  fof(f35,plain,(
% 39.51/5.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f26])).
% 39.51/5.51  
% 39.51/5.51  fof(f1,axiom,(
% 39.51/5.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f11,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 39.51/5.51    inference(ennf_transformation,[],[f1])).
% 39.51/5.51  
% 39.51/5.51  fof(f34,plain,(
% 39.51/5.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f11])).
% 39.51/5.51  
% 39.51/5.51  fof(f57,plain,(
% 39.51/5.51    m1_pre_topc(sK3,sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f53,plain,(
% 39.51/5.51    m1_pre_topc(sK1,sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f3,axiom,(
% 39.51/5.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f13,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f3])).
% 39.51/5.51  
% 39.51/5.51  fof(f14,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.51/5.51    inference(flattening,[],[f13])).
% 39.51/5.51  
% 39.51/5.51  fof(f27,plain,(
% 39.51/5.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.51/5.51    inference(nnf_transformation,[],[f14])).
% 39.51/5.51  
% 39.51/5.51  fof(f37,plain,(
% 39.51/5.51    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f27])).
% 39.51/5.51  
% 39.51/5.51  fof(f61,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(equality_resolution,[],[f37])).
% 39.51/5.51  
% 39.51/5.51  fof(f4,axiom,(
% 39.51/5.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f15,plain,(
% 39.51/5.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 39.51/5.51    inference(ennf_transformation,[],[f4])).
% 39.51/5.51  
% 39.51/5.51  fof(f16,plain,(
% 39.51/5.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.51/5.51    inference(flattening,[],[f15])).
% 39.51/5.51  
% 39.51/5.51  fof(f39,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f16])).
% 39.51/5.51  
% 39.51/5.51  fof(f40,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f16])).
% 39.51/5.51  
% 39.51/5.51  fof(f41,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f16])).
% 39.51/5.51  
% 39.51/5.51  fof(f49,plain,(
% 39.51/5.51    ~v2_struct_0(sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f51,plain,(
% 39.51/5.51    l1_pre_topc(sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f52,plain,(
% 39.51/5.51    ~v2_struct_0(sK1)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f59,plain,(
% 39.51/5.51    m1_pre_topc(sK3,sK2)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f58,plain,(
% 39.51/5.51    m1_pre_topc(sK1,sK2)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f54,plain,(
% 39.51/5.51    ~v2_struct_0(sK2)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f56,plain,(
% 39.51/5.51    ~v2_struct_0(sK3)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f7,axiom,(
% 39.51/5.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 39.51/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.51/5.51  
% 39.51/5.51  fof(f21,plain,(
% 39.51/5.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 39.51/5.51    inference(ennf_transformation,[],[f7])).
% 39.51/5.51  
% 39.51/5.51  fof(f46,plain,(
% 39.51/5.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f21])).
% 39.51/5.51  
% 39.51/5.51  fof(f47,plain,(
% 39.51/5.51    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.51/5.51    inference(cnf_transformation,[],[f28])).
% 39.51/5.51  
% 39.51/5.51  fof(f60,plain,(
% 39.51/5.51    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  fof(f50,plain,(
% 39.51/5.51    v2_pre_topc(sK0)),
% 39.51/5.51    inference(cnf_transformation,[],[f33])).
% 39.51/5.51  
% 39.51/5.51  cnf(c_389,plain,
% 39.51/5.51      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 39.51/5.51      theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1240,plain,
% 39.51/5.51      ( X0_44 != X1_44
% 39.51/5.51      | X0_44 = u1_struct_0(X0_43)
% 39.51/5.51      | u1_struct_0(X0_43) != X1_44 ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_389]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1347,plain,
% 39.51/5.51      ( X0_44 != u1_struct_0(X0_43)
% 39.51/5.51      | X0_44 = u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(X1_43) != u1_struct_0(X0_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1240]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1500,plain,
% 39.51/5.51      ( u1_struct_0(X0_43) != u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(X2_43) != u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(X0_43) = u1_struct_0(X2_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1347]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3190,plain,
% 39.51/5.51      ( u1_struct_0(X0_43) != u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1500]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5974,plain,
% 39.51/5.51      ( u1_struct_0(X0_43) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3190]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_8017,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_5974]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_132877,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_8017]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_399,plain,
% 39.51/5.51      ( ~ r1_tarski(X0_44,X1_44)
% 39.51/5.51      | r1_tarski(X2_44,X3_44)
% 39.51/5.51      | X2_44 != X0_44
% 39.51/5.51      | X3_44 != X1_44 ),
% 39.51/5.51      theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1158,plain,
% 39.51/5.51      ( r1_tarski(X0_44,X1_44)
% 39.51/5.51      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 39.51/5.51      | X0_44 != u1_struct_0(X0_43)
% 39.51/5.51      | X1_44 != u1_struct_0(X1_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_399]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1242,plain,
% 39.51/5.51      ( r1_tarski(X0_44,u1_struct_0(X0_43))
% 39.51/5.51      | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 39.51/5.51      | X0_44 != u1_struct_0(X1_43)
% 39.51/5.51      | u1_struct_0(X0_43) != u1_struct_0(X2_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1158]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1552,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 39.51/5.51      | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X3_43))
% 39.51/5.51      | u1_struct_0(X2_43) != u1_struct_0(X0_43)
% 39.51/5.51      | u1_struct_0(X3_43) != u1_struct_0(X1_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1242]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_2412,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 39.51/5.51      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43)
% 39.51/5.51      | u1_struct_0(sK2) != u1_struct_0(X1_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1552]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3191,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(X1_43))
% 39.51/5.51      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
% 39.51/5.51      | u1_struct_0(sK2) != u1_struct_0(X1_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_2412]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4350,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
% 39.51/5.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3191]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_68218,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 39.51/5.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_4350]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_13,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 39.51/5.51      | ~ m1_pre_topc(X0,X2)
% 39.51/5.51      | ~ m1_pre_topc(X1,X2)
% 39.51/5.51      | ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ v2_pre_topc(X2)
% 39.51/5.51      | ~ l1_pre_topc(X2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f48]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_374,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 39.51/5.51      | ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ m1_pre_topc(X0_43,X2_43)
% 39.51/5.51      | ~ m1_pre_topc(X1_43,X2_43)
% 39.51/5.51      | ~ v2_pre_topc(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X2_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_13]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3214,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ m1_pre_topc(X0_43,sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X1_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_374]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4393,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,X0_43,X1_43)),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,X0_43,X1_43),X2_43)
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,X0_43,X1_43),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,X2_43)
% 39.51/5.51      | ~ v2_pre_topc(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X2_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3214]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_8636,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_43)
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,X0_43)
% 39.51/5.51      | ~ v2_pre_topc(X0_43)
% 39.51/5.51      | ~ l1_pre_topc(X0_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_4393]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_11685,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 39.51/5.51      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 39.51/5.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_8636]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_32483,plain,
% 39.51/5.51      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_11685]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_11,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ v2_pre_topc(X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | ~ l1_pre_topc(X1)
% 39.51/5.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f45]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_376,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X1_43)
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43)
% 39.51/5.51      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_11]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_398,plain,
% 39.51/5.51      ( ~ v2_pre_topc(X0_43) | v2_pre_topc(X1_43) | X1_43 != X0_43 ),
% 39.51/5.51      theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3996,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X1_43)
% 39.51/5.51      | ~ v2_pre_topc(k1_tsep_1(X1_43,X0_43,X0_43))
% 39.51/5.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(resolution,[status(thm)],[c_376,c_398]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_8,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | ~ v2_pre_topc(X1)
% 39.51/5.51      | v2_pre_topc(k1_tsep_1(X1,X0,X2))
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f44]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_377,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ m1_pre_topc(X2_43,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X1_43)
% 39.51/5.51      | v2_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43))
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | v2_struct_0(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_8]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_9857,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X1_43)
% 39.51/5.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(resolution,[status(thm)],[c_3996,c_377]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_20,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK2,sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f55]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_367,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK2,sK0) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_20]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_11843,plain,
% 39.51/5.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ v2_pre_topc(sK0)
% 39.51/5.51      | v2_struct_0(sK2)
% 39.51/5.51      | v2_struct_0(sK0)
% 39.51/5.51      | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(resolution,[status(thm)],[c_9857,c_367]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_2,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 39.51/5.51      | ~ l1_pre_topc(X0)
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f35]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_0,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f34]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_191,plain,
% 39.51/5.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 39.51/5.51      | ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(global_propositional_subsumption,[status(thm)],[c_2,c_0]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_192,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(renaming,[status(thm)],[c_191]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_360,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_192]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_8123,plain,
% 39.51/5.51      ( m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ m1_pre_topc(X0_43,sK2)
% 39.51/5.51      | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_360]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_10050,plain,
% 39.51/5.51      ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ m1_pre_topc(sK2,sK2)
% 39.51/5.51      | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_8123]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_18,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK3,sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f57]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_369,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK3,sK0) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_18]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_833,plain,
% 39.51/5.51      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_22,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK1,sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f53]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_365,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK1,sK0) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_22]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_837,plain,
% 39.51/5.51      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 39.51/5.51      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 39.51/5.51      | ~ l1_pre_topc(X1)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.51/5.51      inference(cnf_transformation,[],[f61]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_7,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f39]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_6,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f40]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | ~ l1_pre_topc(X1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f41]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_224,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | ~ l1_pre_topc(X1)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.51/5.51      inference(global_propositional_subsumption,
% 39.51/5.51                [status(thm)],
% 39.51/5.51                [c_4,c_7,c_6,c_5]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_225,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ m1_pre_topc(X2,X1)
% 39.51/5.51      | v2_struct_0(X1)
% 39.51/5.51      | v2_struct_0(X0)
% 39.51/5.51      | v2_struct_0(X2)
% 39.51/5.51      | ~ l1_pre_topc(X1)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 39.51/5.51      inference(renaming,[status(thm)],[c_224]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_359,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ m1_pre_topc(X2_43,X1_43)
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | v2_struct_0(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43)
% 39.51/5.51      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_225]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_843,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 39.51/5.51      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 39.51/5.51      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | v2_struct_0(X1_43) = iProver_top
% 39.51/5.51      | v2_struct_0(X2_43) = iProver_top
% 39.51/5.51      | l1_pre_topc(X0_43) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4446,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 39.51/5.51      | m1_pre_topc(X0_43,sK0) != iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | v2_struct_0(sK1) = iProver_top
% 39.51/5.51      | v2_struct_0(sK0) = iProver_top
% 39.51/5.51      | l1_pre_topc(sK0) != iProver_top ),
% 39.51/5.51      inference(superposition,[status(thm)],[c_837,c_843]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_26,negated_conjecture,
% 39.51/5.51      ( ~ v2_struct_0(sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f49]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_27,plain,
% 39.51/5.51      ( v2_struct_0(sK0) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_24,negated_conjecture,
% 39.51/5.51      ( l1_pre_topc(sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f51]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_29,plain,
% 39.51/5.51      ( l1_pre_topc(sK0) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_23,negated_conjecture,
% 39.51/5.51      ( ~ v2_struct_0(sK1) ),
% 39.51/5.51      inference(cnf_transformation,[],[f52]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_30,plain,
% 39.51/5.51      ( v2_struct_0(sK1) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_7131,plain,
% 39.51/5.51      ( v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | m1_pre_topc(X0_43,sK0) != iProver_top
% 39.51/5.51      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
% 39.51/5.51      inference(global_propositional_subsumption,
% 39.51/5.51                [status(thm)],
% 39.51/5.51                [c_4446,c_27,c_29,c_30]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_7132,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 39.51/5.51      | m1_pre_topc(X0_43,sK0) != iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top ),
% 39.51/5.51      inference(renaming,[status(thm)],[c_7131]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_7140,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | v2_struct_0(sK3) = iProver_top ),
% 39.51/5.51      inference(superposition,[status(thm)],[c_833,c_7132]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_16,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK3,sK2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f59]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_371,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK3,sK2) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_16]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_831,plain,
% 39.51/5.51      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_17,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK1,sK2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f58]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_370,negated_conjecture,
% 39.51/5.51      ( m1_pre_topc(sK1,sK2) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_17]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_832,plain,
% 39.51/5.51      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4443,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 39.51/5.51      | m1_pre_topc(X0_43,sK2) != iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | v2_struct_0(sK2) = iProver_top
% 39.51/5.51      | v2_struct_0(sK1) = iProver_top
% 39.51/5.51      | l1_pre_topc(sK2) != iProver_top ),
% 39.51/5.51      inference(superposition,[status(thm)],[c_832,c_843]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_21,negated_conjecture,
% 39.51/5.51      ( ~ v2_struct_0(sK2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f54]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_32,plain,
% 39.51/5.51      ( v2_struct_0(sK2) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_383,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43)
% 39.51/5.51      | l1_pre_topc(X0_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_0]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1190,plain,
% 39.51/5.51      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(resolution,[status(thm)],[c_383,c_367]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1191,plain,
% 39.51/5.51      ( l1_pre_topc(sK2) = iProver_top
% 39.51/5.51      | l1_pre_topc(sK0) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5461,plain,
% 39.51/5.51      ( v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | m1_pre_topc(X0_43,sK2) != iProver_top
% 39.51/5.51      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
% 39.51/5.51      inference(global_propositional_subsumption,
% 39.51/5.51                [status(thm)],
% 39.51/5.51                [c_4443,c_29,c_30,c_32,c_1191]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5462,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 39.51/5.51      | m1_pre_topc(X0_43,sK2) != iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top ),
% 39.51/5.51      inference(renaming,[status(thm)],[c_5461]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5470,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 39.51/5.51      | v2_struct_0(sK3) = iProver_top ),
% 39.51/5.51      inference(superposition,[status(thm)],[c_831,c_5462]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_19,negated_conjecture,
% 39.51/5.51      ( ~ v2_struct_0(sK3) ),
% 39.51/5.51      inference(cnf_transformation,[],[f56]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_34,plain,
% 39.51/5.51      ( v2_struct_0(sK3) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5628,plain,
% 39.51/5.51      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 39.51/5.51      inference(global_propositional_subsumption,
% 39.51/5.51                [status(thm)],
% 39.51/5.51                [c_5470,c_34]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_7189,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | v2_struct_0(sK3) = iProver_top ),
% 39.51/5.51      inference(demodulation,[status(thm)],[c_7140,c_5628]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3629,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43),sK2)
% 39.51/5.51      | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_360]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_5401,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 39.51/5.51      | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3629]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_380,plain,
% 39.51/5.51      ( ~ m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ m1_pre_topc(X2_43,X1_43)
% 39.51/5.51      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 39.51/5.51      | v2_struct_0(X1_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | v2_struct_0(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_5]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4767,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(X0_43,sK2,sK2),X0_43)
% 39.51/5.51      | ~ m1_pre_topc(sK2,X0_43)
% 39.51/5.51      | v2_struct_0(X0_43)
% 39.51/5.51      | v2_struct_0(sK2)
% 39.51/5.51      | ~ l1_pre_topc(X0_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_380]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4769,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
% 39.51/5.51      | ~ m1_pre_topc(sK2,sK0)
% 39.51/5.51      | v2_struct_0(sK2)
% 39.51/5.51      | v2_struct_0(sK0)
% 39.51/5.51      | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_4767]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_12,plain,
% 39.51/5.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f46]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_375,plain,
% 39.51/5.51      ( m1_pre_topc(X0_43,X0_43) | ~ l1_pre_topc(X0_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_12]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4386,plain,
% 39.51/5.51      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_375]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_392,plain,
% 39.51/5.51      ( u1_struct_0(X0_43) = u1_struct_0(X1_43) | X0_43 != X1_43 ),
% 39.51/5.51      theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3186,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_43)
% 39.51/5.51      | k1_tsep_1(sK0,sK1,sK3) != X0_43 ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_392]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_4150,plain,
% 39.51/5.51      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 39.51/5.51      | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3186]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3449,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK3,sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK1,sK2)
% 39.51/5.51      | v2_struct_0(sK2)
% 39.51/5.51      | v2_struct_0(sK3)
% 39.51/5.51      | v2_struct_0(sK1)
% 39.51/5.51      | ~ l1_pre_topc(sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_380]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3437,plain,
% 39.51/5.51      ( ~ m1_pre_topc(k1_tsep_1(X0_43,sK2,sK2),X1_43)
% 39.51/5.51      | ~ l1_pre_topc(X1_43)
% 39.51/5.51      | l1_pre_topc(k1_tsep_1(X0_43,sK2,sK2)) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_383]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_3439,plain,
% 39.51/5.51      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
% 39.51/5.51      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
% 39.51/5.51      | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_3437]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_390,plain,
% 39.51/5.51      ( ~ l1_pre_topc(X0_43) | l1_pre_topc(X1_43) | X1_43 != X0_43 ),
% 39.51/5.51      theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1571,plain,
% 39.51/5.51      ( ~ l1_pre_topc(X0_43)
% 39.51/5.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_390]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_2160,plain,
% 39.51/5.51      ( ~ l1_pre_topc(k1_tsep_1(X0_43,sK2,sK2))
% 39.51/5.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(X0_43,sK2,sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1571]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_2163,plain,
% 39.51/5.51      ( ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
% 39.51/5.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 39.51/5.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_2160]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_2133,plain,
% 39.51/5.51      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_392]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_835,plain,
% 39.51/5.51      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_826,plain,
% 39.51/5.51      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
% 39.51/5.51      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 39.51/5.51      | v2_pre_topc(X1_43) != iProver_top
% 39.51/5.51      | v2_struct_0(X1_43) = iProver_top
% 39.51/5.51      | v2_struct_0(X0_43) = iProver_top
% 39.51/5.51      | l1_pre_topc(X1_43) != iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1705,plain,
% 39.51/5.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 39.51/5.51      | v2_pre_topc(sK0) != iProver_top
% 39.51/5.51      | v2_struct_0(sK2) = iProver_top
% 39.51/5.51      | v2_struct_0(sK0) = iProver_top
% 39.51/5.51      | l1_pre_topc(sK0) != iProver_top ),
% 39.51/5.51      inference(superposition,[status(thm)],[c_835,c_826]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_385,plain,( X0_43 = X0_43 ),theory(equality) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1407,plain,
% 39.51/5.51      ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_385]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1313,plain,
% 39.51/5.51      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 39.51/5.51      | ~ m1_pre_topc(sK3,sK0)
% 39.51/5.51      | ~ m1_pre_topc(sK1,sK0)
% 39.51/5.51      | v2_struct_0(sK3)
% 39.51/5.51      | v2_struct_0(sK1)
% 39.51/5.51      | v2_struct_0(sK0)
% 39.51/5.51      | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_380]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1206,plain,
% 39.51/5.51      ( sK2 = sK2 ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_385]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_14,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 39.51/5.51      | ~ m1_pre_topc(X0,X2)
% 39.51/5.51      | ~ m1_pre_topc(X1,X2)
% 39.51/5.51      | m1_pre_topc(X0,X1)
% 39.51/5.51      | ~ v2_pre_topc(X2)
% 39.51/5.51      | ~ l1_pre_topc(X2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f47]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_373,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 39.51/5.51      | ~ m1_pre_topc(X0_43,X2_43)
% 39.51/5.51      | ~ m1_pre_topc(X1_43,X2_43)
% 39.51/5.51      | m1_pre_topc(X0_43,X1_43)
% 39.51/5.51      | ~ v2_pre_topc(X2_43)
% 39.51/5.51      | ~ l1_pre_topc(X2_43) ),
% 39.51/5.51      inference(subtyping,[status(esa)],[c_14]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1130,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 39.51/5.51      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(sK2,X0_43)
% 39.51/5.51      | ~ v2_pre_topc(X0_43)
% 39.51/5.51      | ~ l1_pre_topc(X0_43) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_373]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_1132,plain,
% 39.51/5.51      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 39.51/5.51      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 39.51/5.51      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 39.51/5.51      | ~ m1_pre_topc(sK2,sK0)
% 39.51/5.51      | ~ v2_pre_topc(sK0)
% 39.51/5.51      | ~ l1_pre_topc(sK0) ),
% 39.51/5.51      inference(instantiation,[status(thm)],[c_1130]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_15,negated_conjecture,
% 39.51/5.51      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 39.51/5.51      inference(cnf_transformation,[],[f60]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_25,negated_conjecture,
% 39.51/5.51      ( v2_pre_topc(sK0) ),
% 39.51/5.51      inference(cnf_transformation,[],[f50]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(c_28,plain,
% 39.51/5.51      ( v2_pre_topc(sK0) = iProver_top ),
% 39.51/5.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.51/5.51  
% 39.51/5.51  cnf(contradiction,plain,
% 39.51/5.51      ( $false ),
% 39.51/5.51      inference(minisat,
% 39.51/5.51                [status(thm)],
% 39.51/5.51                [c_132877,c_68218,c_32483,c_11843,c_10050,c_7189,c_5401,
% 39.51/5.51                 c_4769,c_4386,c_4150,c_3449,c_3439,c_2163,c_2133,c_1705,
% 39.51/5.51                 c_1407,c_1313,c_1206,c_1190,c_1132,c_15,c_16,c_17,c_18,
% 39.51/5.51                 c_34,c_19,c_20,c_32,c_21,c_22,c_23,c_29,c_24,c_28,c_25,
% 39.51/5.51                 c_27,c_26]) ).
% 39.51/5.51  
% 39.51/5.51  
% 39.51/5.51  % SZS output end CNFRefutation for theBenchmark.p
% 39.51/5.51  
% 39.51/5.51  ------                               Statistics
% 39.51/5.51  
% 39.51/5.51  ------ Selected
% 39.51/5.51  
% 39.51/5.51  total_time:                             4.711
% 39.51/5.51  
%------------------------------------------------------------------------------
