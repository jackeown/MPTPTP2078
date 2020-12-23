%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:08 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 463 expanded)
%              Number of clauses        :   90 ( 126 expanded)
%              Number of leaves         :   14 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  610 (4337 expanded)
%              Number of equality atoms :  116 ( 145 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26,f25,f24,f23])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
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
    inference(equality_resolution,[],[f30])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_214,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_960,plain,
    ( X0_42 != X1_42
    | X0_42 = u1_struct_0(X0_41)
    | u1_struct_0(X0_41) != X1_42 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_990,plain,
    ( X0_42 != u1_struct_0(X0_41)
    | X0_42 = u1_struct_0(X1_41)
    | u1_struct_0(X1_41) != u1_struct_0(X0_41) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1220,plain,
    ( u1_struct_0(X0_41) != u1_struct_0(X1_41)
    | u1_struct_0(X2_41) != u1_struct_0(X1_41)
    | u1_struct_0(X0_41) = u1_struct_0(X2_41) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1682,plain,
    ( u1_struct_0(X0_41) != u1_struct_0(X1_41)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X1_41)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_41) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_1810,plain,
    ( u1_struct_0(X0_41) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_41)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_1851,plain,
    ( u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(X0_41,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_17241,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_8,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_202,plain,
    ( r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | ~ m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X0_41,X2_41)
    | ~ m1_pre_topc(X1_41,X2_41)
    | ~ l1_pre_topc(X2_41)
    | ~ v2_pre_topc(X2_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1471,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(X0_41,X1_41,X2_41)),u1_struct_0(X3_41))
    | ~ m1_pre_topc(X3_41,X4_41)
    | ~ m1_pre_topc(k1_tsep_1(X0_41,X1_41,X2_41),X3_41)
    | ~ m1_pre_topc(k1_tsep_1(X0_41,X1_41,X2_41),X4_41)
    | ~ l1_pre_topc(X4_41)
    | ~ v2_pre_topc(X4_41) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_2388,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(X0_41,sK1,sK3),X1_41)
    | ~ m1_pre_topc(k1_tsep_1(X0_41,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X1_41)
    | ~ l1_pre_topc(X1_41)
    | ~ v2_pre_topc(X1_41) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_3573,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_41)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_41)
    | ~ l1_pre_topc(X0_41)
    | ~ v2_pre_topc(X0_41) ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_8880,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3573])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_893,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | X0_42 != u1_struct_0(X0_41)
    | X1_42 != u1_struct_0(X1_41) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_953,plain,
    ( r1_tarski(X0_42,u1_struct_0(X0_41))
    | ~ r1_tarski(u1_struct_0(X1_41),u1_struct_0(X0_41))
    | X0_42 != u1_struct_0(X1_41)
    | u1_struct_0(X0_41) != u1_struct_0(X0_41) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_1058,plain,
    ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | r1_tarski(u1_struct_0(X2_41),u1_struct_0(X1_41))
    | u1_struct_0(X1_41) != u1_struct_0(X1_41)
    | u1_struct_0(X2_41) != u1_struct_0(X0_41) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_1233,plain,
    ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_41)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_1500,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_41,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_6867,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_203,plain,
    ( m1_pre_topc(X0_41,X0_41)
    | ~ l1_pre_topc(X0_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6501,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_197,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_612,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_193,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_616,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_168,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_6,c_5,c_4])).

cnf(c_169,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X2_41,X1_41)
    | v2_struct_0(X1_41)
    | v2_struct_0(X0_41)
    | v2_struct_0(X2_41)
    | ~ l1_pre_topc(X1_41)
    | u1_struct_0(k1_tsep_1(X1_41,X0_41,X2_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X2_41)) ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_621,plain,
    ( u1_struct_0(k1_tsep_1(X0_41,X1_41,X2_41)) = k2_xboole_0(u1_struct_0(X1_41),u1_struct_0(X2_41))
    | m1_pre_topc(X1_41,X0_41) != iProver_top
    | m1_pre_topc(X2_41,X0_41) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(X1_41) = iProver_top
    | v2_struct_0(X2_41) = iProver_top
    | l1_pre_topc(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_2922,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_621])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5646,plain,
    ( v2_struct_0(X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2922,c_22,c_24,c_25])).

cnf(c_5647,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_5646])).

cnf(c_5655,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_5647])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_199,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_610,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_198,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_611,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_2919,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41))
    | m1_pre_topc(X0_41,sK2) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_621])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_208,plain,
    ( ~ m1_pre_topc(X0_41,X1_41)
    | ~ l1_pre_topc(X1_41)
    | l1_pre_topc(X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_195,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_948,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_208,c_195])).

cnf(c_949,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_4270,plain,
    ( v2_struct_0(X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2919,c_24,c_25,c_27,c_949])).

cnf(c_4271,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41))
    | m1_pre_topc(X0_41,sK2) != iProver_top
    | v2_struct_0(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_4270])).

cnf(c_4279,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_4271])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4320,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4279,c_29])).

cnf(c_5694,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5655,c_4320])).

cnf(c_206,plain,
    ( ~ m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X2_41,X1_41)
    | m1_pre_topc(k1_tsep_1(X1_41,X0_41,X2_41),X1_41)
    | v2_struct_0(X1_41)
    | v2_struct_0(X0_41)
    | v2_struct_0(X2_41)
    | ~ l1_pre_topc(X1_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2901,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_2571,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_212,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_954,plain,
    ( u1_struct_0(X0_41) = u1_struct_0(X0_41) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_1751,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1264,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_614,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_209,plain,
    ( ~ m1_pre_topc(X0_41,X1_41)
    | ~ l1_pre_topc(X1_41)
    | ~ v2_pre_topc(X1_41)
    | v2_pre_topc(X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_600,plain,
    ( m1_pre_topc(X0_41,X1_41) != iProver_top
    | l1_pre_topc(X1_41) != iProver_top
    | v2_pre_topc(X1_41) != iProver_top
    | v2_pre_topc(X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_1000,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_600])).

cnf(c_1028,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1000])).

cnf(c_9,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_201,plain,
    ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | ~ m1_pre_topc(X0_41,X2_41)
    | ~ m1_pre_topc(X1_41,X2_41)
    | m1_pre_topc(X0_41,X1_41)
    | ~ l1_pre_topc(X2_41)
    | ~ v2_pre_topc(X2_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_849,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_41)
    | ~ l1_pre_topc(X0_41)
    | ~ v2_pre_topc(X0_41) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_851,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_10,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17241,c_8880,c_6867,c_6501,c_5694,c_2901,c_2571,c_1751,c_1264,c_1028,c_948,c_851,c_10,c_11,c_12,c_13,c_29,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:20:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.54/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.49  
% 7.54/1.49  ------  iProver source info
% 7.54/1.49  
% 7.54/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.49  git: non_committed_changes: false
% 7.54/1.49  git: last_make_outside_of_git: false
% 7.54/1.49  
% 7.54/1.49  ------ 
% 7.54/1.49  ------ Parsing...
% 7.54/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  ------ Proving...
% 7.54/1.49  ------ Problem Properties 
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  clauses                                 22
% 7.54/1.49  conjectures                             12
% 7.54/1.49  EPR                                     14
% 7.54/1.49  Horn                                    17
% 7.54/1.49  unary                                   12
% 7.54/1.49  binary                                  1
% 7.54/1.49  lits                                    72
% 7.54/1.49  lits eq                                 3
% 7.54/1.49  fd_pure                                 0
% 7.54/1.49  fd_pseudo                               0
% 7.54/1.49  fd_cond                                 0
% 7.54/1.49  fd_pseudo_cond                          1
% 7.54/1.49  AC symbols                              0
% 7.54/1.49  
% 7.54/1.49  ------ Input Options Time Limit: Unbounded
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ 
% 7.54/1.49  Current options:
% 7.54/1.49  ------ 
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS status Theorem for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  fof(f6,axiom,(
% 7.54/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f17,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f6])).
% 7.54/1.49  
% 7.54/1.49  fof(f18,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.54/1.49    inference(flattening,[],[f17])).
% 7.54/1.49  
% 7.54/1.49  fof(f22,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.54/1.49    inference(nnf_transformation,[],[f18])).
% 7.54/1.49  
% 7.54/1.49  fof(f37,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f22])).
% 7.54/1.49  
% 7.54/1.49  fof(f5,axiom,(
% 7.54/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f16,plain,(
% 7.54/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f5])).
% 7.54/1.49  
% 7.54/1.49  fof(f35,plain,(
% 7.54/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f16])).
% 7.54/1.49  
% 7.54/1.49  fof(f7,conjecture,(
% 7.54/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f8,negated_conjecture,(
% 7.54/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.54/1.49    inference(negated_conjecture,[],[f7])).
% 7.54/1.49  
% 7.54/1.49  fof(f19,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f8])).
% 7.54/1.49  
% 7.54/1.49  fof(f20,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.54/1.49    inference(flattening,[],[f19])).
% 7.54/1.49  
% 7.54/1.49  fof(f26,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f25,plain,(
% 7.54/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f24,plain,(
% 7.54/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f23,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f27,plain,(
% 7.54/1.49    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26,f25,f24,f23])).
% 7.54/1.49  
% 7.54/1.49  fof(f46,plain,(
% 7.54/1.49    m1_pre_topc(sK3,sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f42,plain,(
% 7.54/1.49    m1_pre_topc(sK1,sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f3,axiom,(
% 7.54/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f12,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f3])).
% 7.54/1.49  
% 7.54/1.49  fof(f13,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.49    inference(flattening,[],[f12])).
% 7.54/1.49  
% 7.54/1.49  fof(f21,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.49    inference(nnf_transformation,[],[f13])).
% 7.54/1.49  
% 7.54/1.49  fof(f30,plain,(
% 7.54/1.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f21])).
% 7.54/1.49  
% 7.54/1.49  fof(f50,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.49    inference(equality_resolution,[],[f30])).
% 7.54/1.49  
% 7.54/1.49  fof(f4,axiom,(
% 7.54/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f14,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f4])).
% 7.54/1.49  
% 7.54/1.49  fof(f15,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.49    inference(flattening,[],[f14])).
% 7.54/1.49  
% 7.54/1.49  fof(f32,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f15])).
% 7.54/1.49  
% 7.54/1.49  fof(f33,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f15])).
% 7.54/1.49  
% 7.54/1.49  fof(f34,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f15])).
% 7.54/1.49  
% 7.54/1.49  fof(f38,plain,(
% 7.54/1.49    ~v2_struct_0(sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f40,plain,(
% 7.54/1.49    l1_pre_topc(sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f41,plain,(
% 7.54/1.49    ~v2_struct_0(sK1)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f48,plain,(
% 7.54/1.49    m1_pre_topc(sK3,sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f47,plain,(
% 7.54/1.49    m1_pre_topc(sK1,sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f43,plain,(
% 7.54/1.49    ~v2_struct_0(sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f2,axiom,(
% 7.54/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f11,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f2])).
% 7.54/1.49  
% 7.54/1.49  fof(f29,plain,(
% 7.54/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f11])).
% 7.54/1.49  
% 7.54/1.49  fof(f44,plain,(
% 7.54/1.49    m1_pre_topc(sK2,sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f45,plain,(
% 7.54/1.49    ~v2_struct_0(sK3)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f1,axiom,(
% 7.54/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f9,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f1])).
% 7.54/1.49  
% 7.54/1.49  fof(f10,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.54/1.49    inference(flattening,[],[f9])).
% 7.54/1.49  
% 7.54/1.49  fof(f28,plain,(
% 7.54/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f10])).
% 7.54/1.49  
% 7.54/1.49  fof(f36,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f22])).
% 7.54/1.49  
% 7.54/1.49  fof(f49,plain,(
% 7.54/1.49    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f39,plain,(
% 7.54/1.49    v2_pre_topc(sK0)),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  cnf(c_214,plain,
% 7.54/1.49      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 7.54/1.49      theory(equality) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_960,plain,
% 7.54/1.49      ( X0_42 != X1_42
% 7.54/1.49      | X0_42 = u1_struct_0(X0_41)
% 7.54/1.49      | u1_struct_0(X0_41) != X1_42 ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_214]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_990,plain,
% 7.54/1.49      ( X0_42 != u1_struct_0(X0_41)
% 7.54/1.49      | X0_42 = u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(X1_41) != u1_struct_0(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_960]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1220,plain,
% 7.54/1.49      ( u1_struct_0(X0_41) != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(X2_41) != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(X0_41) = u1_struct_0(X2_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_990]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1682,plain,
% 7.54/1.49      ( u1_struct_0(X0_41) != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1220]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1810,plain,
% 7.54/1.49      ( u1_struct_0(X0_41) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(X0_41)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1682]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1851,plain,
% 7.54/1.49      ( u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(X0_41,sK1,sK3))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1810]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_17241,plain,
% 7.54/1.49      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1851]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.49      | ~ m1_pre_topc(X0,X2)
% 7.54/1.49      | ~ m1_pre_topc(X1,X2)
% 7.54/1.49      | ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ l1_pre_topc(X2)
% 7.54/1.49      | ~ v2_pre_topc(X2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_202,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
% 7.54/1.49      | ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ m1_pre_topc(X0_41,X2_41)
% 7.54/1.49      | ~ m1_pre_topc(X1_41,X2_41)
% 7.54/1.49      | ~ l1_pre_topc(X2_41)
% 7.54/1.49      | ~ v2_pre_topc(X2_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1471,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(k1_tsep_1(X0_41,X1_41,X2_41)),u1_struct_0(X3_41))
% 7.54/1.49      | ~ m1_pre_topc(X3_41,X4_41)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(X0_41,X1_41,X2_41),X3_41)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(X0_41,X1_41,X2_41),X4_41)
% 7.54/1.49      | ~ l1_pre_topc(X4_41)
% 7.54/1.49      | ~ v2_pre_topc(X4_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_202]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2388,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(X0_41,sK1,sK3),X1_41)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(X0_41,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK2,X1_41)
% 7.54/1.49      | ~ l1_pre_topc(X1_41)
% 7.54/1.49      | ~ v2_pre_topc(X1_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1471]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3573,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_41)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK2,X0_41)
% 7.54/1.49      | ~ l1_pre_topc(X0_41)
% 7.54/1.49      | ~ v2_pre_topc(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2388]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8880,plain,
% 7.54/1.49      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.54/1.49      | ~ l1_pre_topc(sK2)
% 7.54/1.49      | ~ v2_pre_topc(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3573]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_223,plain,
% 7.54/1.49      ( ~ r1_tarski(X0_42,X1_42)
% 7.54/1.49      | r1_tarski(X2_42,X3_42)
% 7.54/1.49      | X2_42 != X0_42
% 7.54/1.49      | X3_42 != X1_42 ),
% 7.54/1.49      theory(equality) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_893,plain,
% 7.54/1.49      ( r1_tarski(X0_42,X1_42)
% 7.54/1.49      | ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
% 7.54/1.49      | X0_42 != u1_struct_0(X0_41)
% 7.54/1.49      | X1_42 != u1_struct_0(X1_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_223]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_953,plain,
% 7.54/1.49      ( r1_tarski(X0_42,u1_struct_0(X0_41))
% 7.54/1.49      | ~ r1_tarski(u1_struct_0(X1_41),u1_struct_0(X0_41))
% 7.54/1.49      | X0_42 != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(X0_41) != u1_struct_0(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_893]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1058,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
% 7.54/1.49      | r1_tarski(u1_struct_0(X2_41),u1_struct_0(X1_41))
% 7.54/1.49      | u1_struct_0(X1_41) != u1_struct_0(X1_41)
% 7.54/1.49      | u1_struct_0(X2_41) != u1_struct_0(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_953]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1233,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(sK2))
% 7.54/1.49      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_41)
% 7.54/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1058]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1500,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_41,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_41,sK1,sK3))
% 7.54/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1233]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6867,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 7.54/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_1500]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_7,plain,
% 7.54/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_203,plain,
% 7.54/1.49      ( m1_pre_topc(X0_41,X0_41) | ~ l1_pre_topc(X0_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6501,plain,
% 7.54/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_203]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_13,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_197,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_612,plain,
% 7.54/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_17,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK1,sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_193,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK1,sK0) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_616,plain,
% 7.54/1.49      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.54/1.49      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.54/1.49      | ~ l1_pre_topc(X1)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.54/1.49      | ~ l1_pre_topc(X1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.54/1.49      | ~ l1_pre_topc(X1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | ~ l1_pre_topc(X1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_168,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | ~ l1_pre_topc(X1)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_3,c_6,c_5,c_4]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_169,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ m1_pre_topc(X2,X1)
% 7.54/1.49      | v2_struct_0(X1)
% 7.54/1.49      | v2_struct_0(X0)
% 7.54/1.49      | v2_struct_0(X2)
% 7.54/1.49      | ~ l1_pre_topc(X1)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_168]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_188,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ m1_pre_topc(X2_41,X1_41)
% 7.54/1.49      | v2_struct_0(X1_41)
% 7.54/1.49      | v2_struct_0(X0_41)
% 7.54/1.49      | v2_struct_0(X2_41)
% 7.54/1.49      | ~ l1_pre_topc(X1_41)
% 7.54/1.49      | u1_struct_0(k1_tsep_1(X1_41,X0_41,X2_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X2_41)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_169]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_621,plain,
% 7.54/1.49      ( u1_struct_0(k1_tsep_1(X0_41,X1_41,X2_41)) = k2_xboole_0(u1_struct_0(X1_41),u1_struct_0(X2_41))
% 7.54/1.49      | m1_pre_topc(X1_41,X0_41) != iProver_top
% 7.54/1.49      | m1_pre_topc(X2_41,X0_41) != iProver_top
% 7.54/1.49      | v2_struct_0(X0_41) = iProver_top
% 7.54/1.49      | v2_struct_0(X1_41) = iProver_top
% 7.54/1.49      | v2_struct_0(X2_41) = iProver_top
% 7.54/1.49      | l1_pre_topc(X0_41) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2922,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
% 7.54/1.49      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.49      | v2_struct_0(X0_41) = iProver_top
% 7.54/1.49      | v2_struct_0(sK1) = iProver_top
% 7.54/1.49      | v2_struct_0(sK0) = iProver_top
% 7.54/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_616,c_621]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_21,negated_conjecture,
% 7.54/1.49      ( ~ v2_struct_0(sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_22,plain,
% 7.54/1.49      ( v2_struct_0(sK0) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_19,negated_conjecture,
% 7.54/1.49      ( l1_pre_topc(sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_24,plain,
% 7.54/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_18,negated_conjecture,
% 7.54/1.49      ( ~ v2_struct_0(sK1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_25,plain,
% 7.54/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5646,plain,
% 7.54/1.49      ( v2_struct_0(X0_41) = iProver_top
% 7.54/1.49      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.49      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_2922,c_22,c_24,c_25]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5647,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_41))
% 7.54/1.49      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.49      | v2_struct_0(X0_41) = iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_5646]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5655,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.54/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_612,c_5647]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_11,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK3,sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_199,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK3,sK2) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_610,plain,
% 7.54/1.49      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_12,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK1,sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_198,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK1,sK2) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_611,plain,
% 7.54/1.49      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2919,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41))
% 7.54/1.49      | m1_pre_topc(X0_41,sK2) != iProver_top
% 7.54/1.49      | v2_struct_0(X0_41) = iProver_top
% 7.54/1.49      | v2_struct_0(sK2) = iProver_top
% 7.54/1.49      | v2_struct_0(sK1) = iProver_top
% 7.54/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_611,c_621]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_16,negated_conjecture,
% 7.54/1.49      ( ~ v2_struct_0(sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_27,plain,
% 7.54/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_208,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ l1_pre_topc(X1_41)
% 7.54/1.49      | l1_pre_topc(X0_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_195,negated_conjecture,
% 7.54/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_948,plain,
% 7.54/1.49      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 7.54/1.49      inference(resolution,[status(thm)],[c_208,c_195]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_949,plain,
% 7.54/1.49      ( l1_pre_topc(sK2) = iProver_top
% 7.54/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4270,plain,
% 7.54/1.49      ( v2_struct_0(X0_41) = iProver_top
% 7.54/1.49      | m1_pre_topc(X0_41,sK2) != iProver_top
% 7.54/1.49      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41)) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_2919,c_24,c_25,c_27,c_949]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4271,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_41))
% 7.54/1.49      | m1_pre_topc(X0_41,sK2) != iProver_top
% 7.54/1.49      | v2_struct_0(X0_41) = iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_4270]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4279,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 7.54/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_610,c_4271]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_14,negated_conjecture,
% 7.54/1.49      ( ~ v2_struct_0(sK3) ),
% 7.54/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_29,plain,
% 7.54/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4320,plain,
% 7.54/1.49      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_4279,c_29]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5694,plain,
% 7.54/1.49      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 7.54/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.54/1.49      inference(demodulation,[status(thm)],[c_5655,c_4320]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_206,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ m1_pre_topc(X2_41,X1_41)
% 7.54/1.49      | m1_pre_topc(k1_tsep_1(X1_41,X0_41,X2_41),X1_41)
% 7.54/1.49      | v2_struct_0(X1_41)
% 7.54/1.49      | v2_struct_0(X0_41)
% 7.54/1.49      | v2_struct_0(X2_41)
% 7.54/1.49      | ~ l1_pre_topc(X1_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2901,plain,
% 7.54/1.49      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.54/1.49      | ~ m1_pre_topc(sK3,sK0)
% 7.54/1.49      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.49      | v2_struct_0(sK3)
% 7.54/1.49      | v2_struct_0(sK1)
% 7.54/1.49      | v2_struct_0(sK0)
% 7.54/1.49      | ~ l1_pre_topc(sK0) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_206]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2571,plain,
% 7.54/1.49      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK3,sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK1,sK2)
% 7.54/1.49      | v2_struct_0(sK2)
% 7.54/1.49      | v2_struct_0(sK3)
% 7.54/1.49      | v2_struct_0(sK1)
% 7.54/1.49      | ~ l1_pre_topc(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_206]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_212,plain,( X0_42 = X0_42 ),theory(equality) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_954,plain,
% 7.54/1.49      ( u1_struct_0(X0_41) = u1_struct_0(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_212]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1751,plain,
% 7.54/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_954]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1264,plain,
% 7.54/1.49      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_954]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_614,plain,
% 7.54/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_0,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ l1_pre_topc(X1)
% 7.54/1.49      | ~ v2_pre_topc(X1)
% 7.54/1.49      | v2_pre_topc(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_209,plain,
% 7.54/1.49      ( ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ l1_pre_topc(X1_41)
% 7.54/1.49      | ~ v2_pre_topc(X1_41)
% 7.54/1.49      | v2_pre_topc(X0_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_600,plain,
% 7.54/1.49      ( m1_pre_topc(X0_41,X1_41) != iProver_top
% 7.54/1.49      | l1_pre_topc(X1_41) != iProver_top
% 7.54/1.49      | v2_pre_topc(X1_41) != iProver_top
% 7.54/1.49      | v2_pre_topc(X0_41) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1000,plain,
% 7.54/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.54/1.49      | v2_pre_topc(sK2) = iProver_top
% 7.54/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_614,c_600]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1028,plain,
% 7.54/1.49      ( ~ l1_pre_topc(sK0) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK0) ),
% 7.54/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1000]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.49      | ~ m1_pre_topc(X0,X2)
% 7.54/1.49      | ~ m1_pre_topc(X1,X2)
% 7.54/1.49      | m1_pre_topc(X0,X1)
% 7.54/1.49      | ~ l1_pre_topc(X2)
% 7.54/1.49      | ~ v2_pre_topc(X2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_201,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41))
% 7.54/1.49      | ~ m1_pre_topc(X0_41,X2_41)
% 7.54/1.49      | ~ m1_pre_topc(X1_41,X2_41)
% 7.54/1.49      | m1_pre_topc(X0_41,X1_41)
% 7.54/1.49      | ~ l1_pre_topc(X2_41)
% 7.54/1.49      | ~ v2_pre_topc(X2_41) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_849,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41)
% 7.54/1.49      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(sK2,X0_41)
% 7.54/1.49      | ~ l1_pre_topc(X0_41)
% 7.54/1.49      | ~ v2_pre_topc(X0_41) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_201]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_851,plain,
% 7.54/1.49      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 7.54/1.49      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 7.54/1.49      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.54/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.54/1.49      | ~ l1_pre_topc(sK0)
% 7.54/1.49      | ~ v2_pre_topc(sK0) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_849]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_10,negated_conjecture,
% 7.54/1.49      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20,negated_conjecture,
% 7.54/1.49      ( v2_pre_topc(sK0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(contradiction,plain,
% 7.54/1.49      ( $false ),
% 7.54/1.49      inference(minisat,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_17241,c_8880,c_6867,c_6501,c_5694,c_2901,c_2571,
% 7.54/1.49                 c_1751,c_1264,c_1028,c_948,c_851,c_10,c_11,c_12,c_13,
% 7.54/1.49                 c_29,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21]) ).
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  ------                               Statistics
% 7.54/1.49  
% 7.54/1.49  ------ Selected
% 7.54/1.49  
% 7.54/1.49  total_time:                             0.542
% 7.54/1.49  
%------------------------------------------------------------------------------
