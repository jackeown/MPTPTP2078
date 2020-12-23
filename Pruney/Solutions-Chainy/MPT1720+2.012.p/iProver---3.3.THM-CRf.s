%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:09 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 446 expanded)
%              Number of clauses        :   79 ( 113 expanded)
%              Number of leaves         :   15 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  636 (4272 expanded)
%              Number of equality atoms :   76 (  96 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31,f30,f29,f28])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_134,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6,c_5])).

cnf(c_135,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_595,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_135])).

cnf(c_29873,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_xboole_0(X2,X0),k2_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_614,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X3_44)
    | r1_tarski(k2_xboole_0(X2_44,X0_44),k2_xboole_0(X3_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1291,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(k2_xboole_0(X0_44,u1_struct_0(X0_43)),k2_xboole_0(X1_44,u1_struct_0(X1_43)))
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1334,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X2_43))
    | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X3_43)) ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_14370,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_622,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_1528,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
    | X0_44 != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | X1_44 != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1945,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
    | r1_tarski(u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)),X0_44)
    | X0_44 != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43))
    | u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)) != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_2673,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
    | r1_tarski(u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)),u1_struct_0(k1_tsep_1(X5_43,X2_43,X3_43)))
    | u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)) != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | u1_struct_0(k1_tsep_1(X5_43,X2_43,X3_43)) != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)) ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_7226,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_601,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1053,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1059,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_3761,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1059])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6074,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_24,c_26,c_29])).

cnf(c_6075,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_6074])).

cnf(c_6084,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_6075])).

cnf(c_610,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4567,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_254,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_255,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_257,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_21])).

cnf(c_258,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_594,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_4462,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_624,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1407,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != X0_43
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1512,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_2102,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_298,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_299,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_303,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_23,c_21])).

cnf(c_592,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | v2_struct_0(X0_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_1785,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_274,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_275,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_279,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_21])).

cnf(c_280,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_593,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_1507,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_1736,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_1733,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_616,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1513,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_613,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1318,plain,
    ( ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1320,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_1305,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_2,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_612,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1265,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29873,c_14370,c_7226,c_6084,c_4567,c_4462,c_2102,c_1785,c_1736,c_1733,c_1513,c_1320,c_1305,c_1265,c_12,c_13,c_14,c_15,c_16,c_17,c_29,c_18,c_19,c_20,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n021.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:54:49 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 7.42/1.46  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/1.46  
% 7.42/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.42/1.46  
% 7.42/1.46  ------  iProver source info
% 7.42/1.46  
% 7.42/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.42/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.42/1.46  git: non_committed_changes: false
% 7.42/1.46  git: last_make_outside_of_git: false
% 7.42/1.46  
% 7.42/1.46  ------ 
% 7.42/1.46  
% 7.42/1.46  ------ Input Options
% 7.42/1.46  
% 7.42/1.46  --out_options                           all
% 7.42/1.46  --tptp_safe_out                         true
% 7.42/1.46  --problem_path                          ""
% 7.42/1.46  --include_path                          ""
% 7.42/1.46  --clausifier                            res/vclausify_rel
% 7.42/1.46  --clausifier_options                    --mode clausify
% 7.42/1.46  --stdin                                 false
% 7.42/1.46  --stats_out                             all
% 7.42/1.46  
% 7.42/1.46  ------ General Options
% 7.42/1.46  
% 7.42/1.46  --fof                                   false
% 7.42/1.46  --time_out_real                         305.
% 7.42/1.46  --time_out_virtual                      -1.
% 7.42/1.46  --symbol_type_check                     false
% 7.42/1.46  --clausify_out                          false
% 7.42/1.46  --sig_cnt_out                           false
% 7.42/1.46  --trig_cnt_out                          false
% 7.42/1.46  --trig_cnt_out_tolerance                1.
% 7.42/1.46  --trig_cnt_out_sk_spl                   false
% 7.42/1.46  --abstr_cl_out                          false
% 7.42/1.46  
% 7.42/1.46  ------ Global Options
% 7.42/1.46  
% 7.42/1.46  --schedule                              default
% 7.42/1.46  --add_important_lit                     false
% 7.42/1.46  --prop_solver_per_cl                    1000
% 7.42/1.46  --min_unsat_core                        false
% 7.42/1.46  --soft_assumptions                      false
% 7.42/1.46  --soft_lemma_size                       3
% 7.42/1.46  --prop_impl_unit_size                   0
% 7.42/1.46  --prop_impl_unit                        []
% 7.42/1.46  --share_sel_clauses                     true
% 7.42/1.46  --reset_solvers                         false
% 7.42/1.46  --bc_imp_inh                            [conj_cone]
% 7.42/1.46  --conj_cone_tolerance                   3.
% 7.42/1.46  --extra_neg_conj                        none
% 7.42/1.46  --large_theory_mode                     true
% 7.42/1.46  --prolific_symb_bound                   200
% 7.42/1.46  --lt_threshold                          2000
% 7.42/1.46  --clause_weak_htbl                      true
% 7.42/1.46  --gc_record_bc_elim                     false
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing Options
% 7.42/1.46  
% 7.42/1.46  --preprocessing_flag                    true
% 7.42/1.46  --time_out_prep_mult                    0.1
% 7.42/1.46  --splitting_mode                        input
% 7.42/1.46  --splitting_grd                         true
% 7.42/1.46  --splitting_cvd                         false
% 7.42/1.46  --splitting_cvd_svl                     false
% 7.42/1.46  --splitting_nvd                         32
% 7.42/1.46  --sub_typing                            true
% 7.42/1.46  --prep_gs_sim                           true
% 7.42/1.46  --prep_unflatten                        true
% 7.42/1.46  --prep_res_sim                          true
% 7.42/1.46  --prep_upred                            true
% 7.42/1.46  --prep_sem_filter                       exhaustive
% 7.42/1.46  --prep_sem_filter_out                   false
% 7.42/1.46  --pred_elim                             true
% 7.42/1.46  --res_sim_input                         true
% 7.42/1.46  --eq_ax_congr_red                       true
% 7.42/1.46  --pure_diseq_elim                       true
% 7.42/1.46  --brand_transform                       false
% 7.42/1.46  --non_eq_to_eq                          false
% 7.42/1.46  --prep_def_merge                        true
% 7.42/1.46  --prep_def_merge_prop_impl              false
% 7.42/1.46  --prep_def_merge_mbd                    true
% 7.42/1.46  --prep_def_merge_tr_red                 false
% 7.42/1.46  --prep_def_merge_tr_cl                  false
% 7.42/1.46  --smt_preprocessing                     true
% 7.42/1.46  --smt_ac_axioms                         fast
% 7.42/1.46  --preprocessed_out                      false
% 7.42/1.46  --preprocessed_stats                    false
% 7.42/1.46  
% 7.42/1.46  ------ Abstraction refinement Options
% 7.42/1.46  
% 7.42/1.46  --abstr_ref                             []
% 7.42/1.46  --abstr_ref_prep                        false
% 7.42/1.46  --abstr_ref_until_sat                   false
% 7.42/1.46  --abstr_ref_sig_restrict                funpre
% 7.42/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.46  --abstr_ref_under                       []
% 7.42/1.46  
% 7.42/1.46  ------ SAT Options
% 7.42/1.46  
% 7.42/1.46  --sat_mode                              false
% 7.42/1.46  --sat_fm_restart_options                ""
% 7.42/1.46  --sat_gr_def                            false
% 7.42/1.46  --sat_epr_types                         true
% 7.42/1.46  --sat_non_cyclic_types                  false
% 7.42/1.46  --sat_finite_models                     false
% 7.42/1.46  --sat_fm_lemmas                         false
% 7.42/1.46  --sat_fm_prep                           false
% 7.42/1.46  --sat_fm_uc_incr                        true
% 7.42/1.46  --sat_out_model                         small
% 7.42/1.46  --sat_out_clauses                       false
% 7.42/1.46  
% 7.42/1.46  ------ QBF Options
% 7.42/1.46  
% 7.42/1.46  --qbf_mode                              false
% 7.42/1.46  --qbf_elim_univ                         false
% 7.42/1.46  --qbf_dom_inst                          none
% 7.42/1.46  --qbf_dom_pre_inst                      false
% 7.42/1.46  --qbf_sk_in                             false
% 7.42/1.46  --qbf_pred_elim                         true
% 7.42/1.46  --qbf_split                             512
% 7.42/1.46  
% 7.42/1.46  ------ BMC1 Options
% 7.42/1.46  
% 7.42/1.46  --bmc1_incremental                      false
% 7.42/1.46  --bmc1_axioms                           reachable_all
% 7.42/1.46  --bmc1_min_bound                        0
% 7.42/1.46  --bmc1_max_bound                        -1
% 7.42/1.46  --bmc1_max_bound_default                -1
% 7.42/1.46  --bmc1_symbol_reachability              true
% 7.42/1.46  --bmc1_property_lemmas                  false
% 7.42/1.46  --bmc1_k_induction                      false
% 7.42/1.46  --bmc1_non_equiv_states                 false
% 7.42/1.46  --bmc1_deadlock                         false
% 7.42/1.46  --bmc1_ucm                              false
% 7.42/1.46  --bmc1_add_unsat_core                   none
% 7.42/1.46  --bmc1_unsat_core_children              false
% 7.42/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.46  --bmc1_out_stat                         full
% 7.42/1.46  --bmc1_ground_init                      false
% 7.42/1.46  --bmc1_pre_inst_next_state              false
% 7.42/1.46  --bmc1_pre_inst_state                   false
% 7.42/1.46  --bmc1_pre_inst_reach_state             false
% 7.42/1.46  --bmc1_out_unsat_core                   false
% 7.42/1.46  --bmc1_aig_witness_out                  false
% 7.42/1.46  --bmc1_verbose                          false
% 7.42/1.46  --bmc1_dump_clauses_tptp                false
% 7.42/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.46  --bmc1_dump_file                        -
% 7.42/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.46  --bmc1_ucm_extend_mode                  1
% 7.42/1.46  --bmc1_ucm_init_mode                    2
% 7.42/1.46  --bmc1_ucm_cone_mode                    none
% 7.42/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.46  --bmc1_ucm_relax_model                  4
% 7.42/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.46  --bmc1_ucm_layered_model                none
% 7.42/1.46  --bmc1_ucm_max_lemma_size               10
% 7.42/1.46  
% 7.42/1.46  ------ AIG Options
% 7.42/1.46  
% 7.42/1.46  --aig_mode                              false
% 7.42/1.46  
% 7.42/1.46  ------ Instantiation Options
% 7.42/1.46  
% 7.42/1.46  --instantiation_flag                    true
% 7.42/1.46  --inst_sos_flag                         false
% 7.42/1.46  --inst_sos_phase                        true
% 7.42/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.46  --inst_lit_sel_side                     num_symb
% 7.42/1.46  --inst_solver_per_active                1400
% 7.42/1.46  --inst_solver_calls_frac                1.
% 7.42/1.46  --inst_passive_queue_type               priority_queues
% 7.42/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.46  --inst_passive_queues_freq              [25;2]
% 7.42/1.46  --inst_dismatching                      true
% 7.42/1.46  --inst_eager_unprocessed_to_passive     true
% 7.42/1.46  --inst_prop_sim_given                   true
% 7.42/1.46  --inst_prop_sim_new                     false
% 7.42/1.46  --inst_subs_new                         false
% 7.42/1.46  --inst_eq_res_simp                      false
% 7.42/1.46  --inst_subs_given                       false
% 7.42/1.46  --inst_orphan_elimination               true
% 7.42/1.46  --inst_learning_loop_flag               true
% 7.42/1.46  --inst_learning_start                   3000
% 7.42/1.46  --inst_learning_factor                  2
% 7.42/1.46  --inst_start_prop_sim_after_learn       3
% 7.42/1.46  --inst_sel_renew                        solver
% 7.42/1.46  --inst_lit_activity_flag                true
% 7.42/1.46  --inst_restr_to_given                   false
% 7.42/1.46  --inst_activity_threshold               500
% 7.42/1.46  --inst_out_proof                        true
% 7.42/1.46  
% 7.42/1.46  ------ Resolution Options
% 7.42/1.46  
% 7.42/1.46  --resolution_flag                       true
% 7.42/1.46  --res_lit_sel                           adaptive
% 7.42/1.46  --res_lit_sel_side                      none
% 7.42/1.46  --res_ordering                          kbo
% 7.42/1.46  --res_to_prop_solver                    active
% 7.42/1.46  --res_prop_simpl_new                    false
% 7.42/1.46  --res_prop_simpl_given                  true
% 7.42/1.46  --res_passive_queue_type                priority_queues
% 7.42/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.46  --res_passive_queues_freq               [15;5]
% 7.42/1.46  --res_forward_subs                      full
% 7.42/1.46  --res_backward_subs                     full
% 7.42/1.46  --res_forward_subs_resolution           true
% 7.42/1.46  --res_backward_subs_resolution          true
% 7.42/1.46  --res_orphan_elimination                true
% 7.42/1.46  --res_time_limit                        2.
% 7.42/1.46  --res_out_proof                         true
% 7.42/1.46  
% 7.42/1.46  ------ Superposition Options
% 7.42/1.46  
% 7.42/1.46  --superposition_flag                    true
% 7.42/1.46  --sup_passive_queue_type                priority_queues
% 7.42/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.46  --demod_completeness_check              fast
% 7.42/1.46  --demod_use_ground                      true
% 7.42/1.46  --sup_to_prop_solver                    passive
% 7.42/1.46  --sup_prop_simpl_new                    true
% 7.42/1.46  --sup_prop_simpl_given                  true
% 7.42/1.46  --sup_fun_splitting                     false
% 7.42/1.46  --sup_smt_interval                      50000
% 7.42/1.46  
% 7.42/1.46  ------ Superposition Simplification Setup
% 7.42/1.46  
% 7.42/1.46  --sup_indices_passive                   []
% 7.42/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_full_bw                           [BwDemod]
% 7.42/1.46  --sup_immed_triv                        [TrivRules]
% 7.42/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_immed_bw_main                     []
% 7.42/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.46  
% 7.42/1.46  ------ Combination Options
% 7.42/1.46  
% 7.42/1.46  --comb_res_mult                         3
% 7.42/1.46  --comb_sup_mult                         2
% 7.42/1.46  --comb_inst_mult                        10
% 7.42/1.46  
% 7.42/1.46  ------ Debug Options
% 7.42/1.46  
% 7.42/1.46  --dbg_backtrace                         false
% 7.42/1.46  --dbg_dump_prop_clauses                 false
% 7.42/1.46  --dbg_dump_prop_clauses_file            -
% 7.42/1.46  --dbg_out_stat                          false
% 7.42/1.46  ------ Parsing...
% 7.42/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.42/1.46  ------ Proving...
% 7.42/1.46  ------ Problem Properties 
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  clauses                                 23
% 7.42/1.46  conjectures                             11
% 7.42/1.46  EPR                                     12
% 7.42/1.46  Horn                                    17
% 7.42/1.46  unary                                   11
% 7.42/1.46  binary                                  1
% 7.42/1.46  lits                                    72
% 7.42/1.46  lits eq                                 4
% 7.42/1.46  fd_pure                                 0
% 7.42/1.46  fd_pseudo                               0
% 7.42/1.46  fd_cond                                 0
% 7.42/1.46  fd_pseudo_cond                          1
% 7.42/1.46  AC symbols                              0
% 7.42/1.46  
% 7.42/1.46  ------ Schedule dynamic 5 is on 
% 7.42/1.46  
% 7.42/1.46  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  ------ 
% 7.42/1.46  Current options:
% 7.42/1.46  ------ 
% 7.42/1.46  
% 7.42/1.46  ------ Input Options
% 7.42/1.46  
% 7.42/1.46  --out_options                           all
% 7.42/1.46  --tptp_safe_out                         true
% 7.42/1.46  --problem_path                          ""
% 7.42/1.46  --include_path                          ""
% 7.42/1.46  --clausifier                            res/vclausify_rel
% 7.42/1.46  --clausifier_options                    --mode clausify
% 7.42/1.46  --stdin                                 false
% 7.42/1.46  --stats_out                             all
% 7.42/1.46  
% 7.42/1.46  ------ General Options
% 7.42/1.46  
% 7.42/1.46  --fof                                   false
% 7.42/1.46  --time_out_real                         305.
% 7.42/1.46  --time_out_virtual                      -1.
% 7.42/1.46  --symbol_type_check                     false
% 7.42/1.46  --clausify_out                          false
% 7.42/1.46  --sig_cnt_out                           false
% 7.42/1.46  --trig_cnt_out                          false
% 7.42/1.46  --trig_cnt_out_tolerance                1.
% 7.42/1.46  --trig_cnt_out_sk_spl                   false
% 7.42/1.46  --abstr_cl_out                          false
% 7.42/1.46  
% 7.42/1.46  ------ Global Options
% 7.42/1.46  
% 7.42/1.46  --schedule                              default
% 7.42/1.46  --add_important_lit                     false
% 7.42/1.46  --prop_solver_per_cl                    1000
% 7.42/1.46  --min_unsat_core                        false
% 7.42/1.46  --soft_assumptions                      false
% 7.42/1.46  --soft_lemma_size                       3
% 7.42/1.46  --prop_impl_unit_size                   0
% 7.42/1.46  --prop_impl_unit                        []
% 7.42/1.46  --share_sel_clauses                     true
% 7.42/1.46  --reset_solvers                         false
% 7.42/1.46  --bc_imp_inh                            [conj_cone]
% 7.42/1.46  --conj_cone_tolerance                   3.
% 7.42/1.46  --extra_neg_conj                        none
% 7.42/1.46  --large_theory_mode                     true
% 7.42/1.46  --prolific_symb_bound                   200
% 7.42/1.46  --lt_threshold                          2000
% 7.42/1.46  --clause_weak_htbl                      true
% 7.42/1.46  --gc_record_bc_elim                     false
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing Options
% 7.42/1.46  
% 7.42/1.46  --preprocessing_flag                    true
% 7.42/1.46  --time_out_prep_mult                    0.1
% 7.42/1.46  --splitting_mode                        input
% 7.42/1.46  --splitting_grd                         true
% 7.42/1.46  --splitting_cvd                         false
% 7.42/1.46  --splitting_cvd_svl                     false
% 7.42/1.46  --splitting_nvd                         32
% 7.42/1.46  --sub_typing                            true
% 7.42/1.46  --prep_gs_sim                           true
% 7.42/1.46  --prep_unflatten                        true
% 7.42/1.46  --prep_res_sim                          true
% 7.42/1.46  --prep_upred                            true
% 7.42/1.46  --prep_sem_filter                       exhaustive
% 7.42/1.46  --prep_sem_filter_out                   false
% 7.42/1.46  --pred_elim                             true
% 7.42/1.46  --res_sim_input                         true
% 7.42/1.46  --eq_ax_congr_red                       true
% 7.42/1.46  --pure_diseq_elim                       true
% 7.42/1.46  --brand_transform                       false
% 7.42/1.46  --non_eq_to_eq                          false
% 7.42/1.46  --prep_def_merge                        true
% 7.42/1.46  --prep_def_merge_prop_impl              false
% 7.42/1.46  --prep_def_merge_mbd                    true
% 7.42/1.46  --prep_def_merge_tr_red                 false
% 7.42/1.46  --prep_def_merge_tr_cl                  false
% 7.42/1.46  --smt_preprocessing                     true
% 7.42/1.46  --smt_ac_axioms                         fast
% 7.42/1.46  --preprocessed_out                      false
% 7.42/1.46  --preprocessed_stats                    false
% 7.42/1.46  
% 7.42/1.46  ------ Abstraction refinement Options
% 7.42/1.46  
% 7.42/1.46  --abstr_ref                             []
% 7.42/1.46  --abstr_ref_prep                        false
% 7.42/1.46  --abstr_ref_until_sat                   false
% 7.42/1.46  --abstr_ref_sig_restrict                funpre
% 7.42/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.46  --abstr_ref_under                       []
% 7.42/1.46  
% 7.42/1.46  ------ SAT Options
% 7.42/1.46  
% 7.42/1.46  --sat_mode                              false
% 7.42/1.46  --sat_fm_restart_options                ""
% 7.42/1.46  --sat_gr_def                            false
% 7.42/1.46  --sat_epr_types                         true
% 7.42/1.46  --sat_non_cyclic_types                  false
% 7.42/1.46  --sat_finite_models                     false
% 7.42/1.46  --sat_fm_lemmas                         false
% 7.42/1.46  --sat_fm_prep                           false
% 7.42/1.46  --sat_fm_uc_incr                        true
% 7.42/1.46  --sat_out_model                         small
% 7.42/1.46  --sat_out_clauses                       false
% 7.42/1.46  
% 7.42/1.46  ------ QBF Options
% 7.42/1.46  
% 7.42/1.46  --qbf_mode                              false
% 7.42/1.46  --qbf_elim_univ                         false
% 7.42/1.46  --qbf_dom_inst                          none
% 7.42/1.46  --qbf_dom_pre_inst                      false
% 7.42/1.46  --qbf_sk_in                             false
% 7.42/1.46  --qbf_pred_elim                         true
% 7.42/1.46  --qbf_split                             512
% 7.42/1.46  
% 7.42/1.46  ------ BMC1 Options
% 7.42/1.46  
% 7.42/1.46  --bmc1_incremental                      false
% 7.42/1.46  --bmc1_axioms                           reachable_all
% 7.42/1.46  --bmc1_min_bound                        0
% 7.42/1.46  --bmc1_max_bound                        -1
% 7.42/1.46  --bmc1_max_bound_default                -1
% 7.42/1.46  --bmc1_symbol_reachability              true
% 7.42/1.46  --bmc1_property_lemmas                  false
% 7.42/1.46  --bmc1_k_induction                      false
% 7.42/1.46  --bmc1_non_equiv_states                 false
% 7.42/1.46  --bmc1_deadlock                         false
% 7.42/1.46  --bmc1_ucm                              false
% 7.42/1.46  --bmc1_add_unsat_core                   none
% 7.42/1.46  --bmc1_unsat_core_children              false
% 7.42/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.46  --bmc1_out_stat                         full
% 7.42/1.46  --bmc1_ground_init                      false
% 7.42/1.46  --bmc1_pre_inst_next_state              false
% 7.42/1.46  --bmc1_pre_inst_state                   false
% 7.42/1.46  --bmc1_pre_inst_reach_state             false
% 7.42/1.46  --bmc1_out_unsat_core                   false
% 7.42/1.46  --bmc1_aig_witness_out                  false
% 7.42/1.46  --bmc1_verbose                          false
% 7.42/1.46  --bmc1_dump_clauses_tptp                false
% 7.42/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.46  --bmc1_dump_file                        -
% 7.42/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.46  --bmc1_ucm_extend_mode                  1
% 7.42/1.46  --bmc1_ucm_init_mode                    2
% 7.42/1.46  --bmc1_ucm_cone_mode                    none
% 7.42/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.46  --bmc1_ucm_relax_model                  4
% 7.42/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.46  --bmc1_ucm_layered_model                none
% 7.42/1.46  --bmc1_ucm_max_lemma_size               10
% 7.42/1.46  
% 7.42/1.46  ------ AIG Options
% 7.42/1.46  
% 7.42/1.46  --aig_mode                              false
% 7.42/1.46  
% 7.42/1.46  ------ Instantiation Options
% 7.42/1.46  
% 7.42/1.46  --instantiation_flag                    true
% 7.42/1.46  --inst_sos_flag                         false
% 7.42/1.46  --inst_sos_phase                        true
% 7.42/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.46  --inst_lit_sel_side                     none
% 7.42/1.46  --inst_solver_per_active                1400
% 7.42/1.46  --inst_solver_calls_frac                1.
% 7.42/1.46  --inst_passive_queue_type               priority_queues
% 7.42/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.46  --inst_passive_queues_freq              [25;2]
% 7.42/1.46  --inst_dismatching                      true
% 7.42/1.46  --inst_eager_unprocessed_to_passive     true
% 7.42/1.46  --inst_prop_sim_given                   true
% 7.42/1.46  --inst_prop_sim_new                     false
% 7.42/1.46  --inst_subs_new                         false
% 7.42/1.46  --inst_eq_res_simp                      false
% 7.42/1.46  --inst_subs_given                       false
% 7.42/1.46  --inst_orphan_elimination               true
% 7.42/1.46  --inst_learning_loop_flag               true
% 7.42/1.46  --inst_learning_start                   3000
% 7.42/1.46  --inst_learning_factor                  2
% 7.42/1.46  --inst_start_prop_sim_after_learn       3
% 7.42/1.46  --inst_sel_renew                        solver
% 7.42/1.46  --inst_lit_activity_flag                true
% 7.42/1.46  --inst_restr_to_given                   false
% 7.42/1.46  --inst_activity_threshold               500
% 7.42/1.46  --inst_out_proof                        true
% 7.42/1.46  
% 7.42/1.46  ------ Resolution Options
% 7.42/1.46  
% 7.42/1.46  --resolution_flag                       false
% 7.42/1.46  --res_lit_sel                           adaptive
% 7.42/1.46  --res_lit_sel_side                      none
% 7.42/1.46  --res_ordering                          kbo
% 7.42/1.46  --res_to_prop_solver                    active
% 7.42/1.46  --res_prop_simpl_new                    false
% 7.42/1.46  --res_prop_simpl_given                  true
% 7.42/1.46  --res_passive_queue_type                priority_queues
% 7.42/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.46  --res_passive_queues_freq               [15;5]
% 7.42/1.46  --res_forward_subs                      full
% 7.42/1.46  --res_backward_subs                     full
% 7.42/1.46  --res_forward_subs_resolution           true
% 7.42/1.46  --res_backward_subs_resolution          true
% 7.42/1.46  --res_orphan_elimination                true
% 7.42/1.46  --res_time_limit                        2.
% 7.42/1.46  --res_out_proof                         true
% 7.42/1.46  
% 7.42/1.46  ------ Superposition Options
% 7.42/1.46  
% 7.42/1.46  --superposition_flag                    true
% 7.42/1.46  --sup_passive_queue_type                priority_queues
% 7.42/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.46  --demod_completeness_check              fast
% 7.42/1.46  --demod_use_ground                      true
% 7.42/1.46  --sup_to_prop_solver                    passive
% 7.42/1.46  --sup_prop_simpl_new                    true
% 7.42/1.46  --sup_prop_simpl_given                  true
% 7.42/1.46  --sup_fun_splitting                     false
% 7.42/1.46  --sup_smt_interval                      50000
% 7.42/1.46  
% 7.42/1.46  ------ Superposition Simplification Setup
% 7.42/1.46  
% 7.42/1.46  --sup_indices_passive                   []
% 7.42/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_full_bw                           [BwDemod]
% 7.42/1.46  --sup_immed_triv                        [TrivRules]
% 7.42/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_immed_bw_main                     []
% 7.42/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.46  
% 7.42/1.46  ------ Combination Options
% 7.42/1.46  
% 7.42/1.46  --comb_res_mult                         3
% 7.42/1.46  --comb_sup_mult                         2
% 7.42/1.46  --comb_inst_mult                        10
% 7.42/1.46  
% 7.42/1.46  ------ Debug Options
% 7.42/1.46  
% 7.42/1.46  --dbg_backtrace                         false
% 7.42/1.46  --dbg_dump_prop_clauses                 false
% 7.42/1.46  --dbg_dump_prop_clauses_file            -
% 7.42/1.46  --dbg_out_stat                          false
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  ------ Proving...
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  % SZS status Theorem for theBenchmark.p
% 7.42/1.46  
% 7.42/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.42/1.46  
% 7.42/1.46  fof(f4,axiom,(
% 7.42/1.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f15,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.42/1.46    inference(ennf_transformation,[],[f4])).
% 7.42/1.46  
% 7.42/1.46  fof(f16,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.42/1.46    inference(flattening,[],[f15])).
% 7.42/1.46  
% 7.42/1.46  fof(f26,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.42/1.46    inference(nnf_transformation,[],[f16])).
% 7.42/1.46  
% 7.42/1.46  fof(f36,plain,(
% 7.42/1.46    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f26])).
% 7.42/1.46  
% 7.42/1.46  fof(f57,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(equality_resolution,[],[f36])).
% 7.42/1.46  
% 7.42/1.46  fof(f5,axiom,(
% 7.42/1.46    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f17,plain,(
% 7.42/1.46    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.42/1.46    inference(ennf_transformation,[],[f5])).
% 7.42/1.46  
% 7.42/1.46  fof(f18,plain,(
% 7.42/1.46    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.42/1.46    inference(flattening,[],[f17])).
% 7.42/1.46  
% 7.42/1.46  fof(f38,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f18])).
% 7.42/1.46  
% 7.42/1.46  fof(f39,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f18])).
% 7.42/1.46  
% 7.42/1.46  fof(f40,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f18])).
% 7.42/1.46  
% 7.42/1.46  fof(f1,axiom,(
% 7.42/1.46    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f11,plain,(
% 7.42/1.46    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 7.42/1.46    inference(ennf_transformation,[],[f1])).
% 7.42/1.46  
% 7.42/1.46  fof(f12,plain,(
% 7.42/1.46    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 7.42/1.46    inference(flattening,[],[f11])).
% 7.42/1.46  
% 7.42/1.46  fof(f33,plain,(
% 7.42/1.46    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f12])).
% 7.42/1.46  
% 7.42/1.46  fof(f9,conjecture,(
% 7.42/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f10,negated_conjecture,(
% 7.42/1.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.42/1.46    inference(negated_conjecture,[],[f9])).
% 7.42/1.46  
% 7.42/1.46  fof(f24,plain,(
% 7.42/1.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.42/1.46    inference(ennf_transformation,[],[f10])).
% 7.42/1.46  
% 7.42/1.46  fof(f25,plain,(
% 7.42/1.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.42/1.46    inference(flattening,[],[f24])).
% 7.42/1.46  
% 7.42/1.46  fof(f31,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.42/1.46    introduced(choice_axiom,[])).
% 7.42/1.46  
% 7.42/1.46  fof(f30,plain,(
% 7.42/1.46    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.42/1.46    introduced(choice_axiom,[])).
% 7.42/1.46  
% 7.42/1.46  fof(f29,plain,(
% 7.42/1.46    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 7.42/1.46    introduced(choice_axiom,[])).
% 7.42/1.46  
% 7.42/1.46  fof(f28,plain,(
% 7.42/1.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.42/1.46    introduced(choice_axiom,[])).
% 7.42/1.46  
% 7.42/1.46  fof(f32,plain,(
% 7.42/1.46    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.42/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31,f30,f29,f28])).
% 7.42/1.46  
% 7.42/1.46  fof(f51,plain,(
% 7.42/1.46    m1_pre_topc(sK2,sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f45,plain,(
% 7.42/1.46    ~v2_struct_0(sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f47,plain,(
% 7.42/1.46    l1_pre_topc(sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f50,plain,(
% 7.42/1.46    ~v2_struct_0(sK2)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f8,axiom,(
% 7.42/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f22,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.42/1.46    inference(ennf_transformation,[],[f8])).
% 7.42/1.46  
% 7.42/1.46  fof(f23,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.42/1.46    inference(flattening,[],[f22])).
% 7.42/1.46  
% 7.42/1.46  fof(f27,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.42/1.46    inference(nnf_transformation,[],[f23])).
% 7.42/1.46  
% 7.42/1.46  fof(f43,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f27])).
% 7.42/1.46  
% 7.42/1.46  fof(f46,plain,(
% 7.42/1.46    v2_pre_topc(sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f6,axiom,(
% 7.42/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f19,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.42/1.46    inference(ennf_transformation,[],[f6])).
% 7.42/1.46  
% 7.42/1.46  fof(f20,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.42/1.46    inference(flattening,[],[f19])).
% 7.42/1.46  
% 7.42/1.46  fof(f41,plain,(
% 7.42/1.46    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f20])).
% 7.42/1.46  
% 7.42/1.46  fof(f44,plain,(
% 7.42/1.46    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f27])).
% 7.42/1.46  
% 7.42/1.46  fof(f2,axiom,(
% 7.42/1.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f13,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.42/1.46    inference(ennf_transformation,[],[f2])).
% 7.42/1.46  
% 7.42/1.46  fof(f34,plain,(
% 7.42/1.46    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f13])).
% 7.42/1.46  
% 7.42/1.46  fof(f3,axiom,(
% 7.42/1.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.42/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.46  
% 7.42/1.46  fof(f14,plain,(
% 7.42/1.46    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.46    inference(ennf_transformation,[],[f3])).
% 7.42/1.46  
% 7.42/1.46  fof(f35,plain,(
% 7.42/1.46    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.46    inference(cnf_transformation,[],[f14])).
% 7.42/1.46  
% 7.42/1.46  fof(f56,plain,(
% 7.42/1.46    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f55,plain,(
% 7.42/1.46    m1_pre_topc(sK3,sK2)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f54,plain,(
% 7.42/1.46    m1_pre_topc(sK1,sK2)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f53,plain,(
% 7.42/1.46    m1_pre_topc(sK3,sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f52,plain,(
% 7.42/1.46    ~v2_struct_0(sK3)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f49,plain,(
% 7.42/1.46    m1_pre_topc(sK1,sK0)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  fof(f48,plain,(
% 7.42/1.46    ~v2_struct_0(sK1)),
% 7.42/1.46    inference(cnf_transformation,[],[f32])).
% 7.42/1.46  
% 7.42/1.46  cnf(c_4,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.42/1.46      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.42/1.46      inference(cnf_transformation,[],[f57]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_7,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f38]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_6,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f39]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_5,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f40]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_134,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.42/1.46      inference(global_propositional_subsumption,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_4,c_7,c_6,c_5]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_135,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X2)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 7.42/1.46      inference(renaming,[status(thm)],[c_134]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_595,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ m1_pre_topc(X2_43,X1_43)
% 7.42/1.46      | v2_struct_0(X0_43)
% 7.42/1.46      | v2_struct_0(X2_43)
% 7.42/1.46      | v2_struct_0(X1_43)
% 7.42/1.46      | ~ l1_pre_topc(X1_43)
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_135]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_29873,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK3,sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK1,sK0)
% 7.42/1.46      | v2_struct_0(sK3)
% 7.42/1.46      | v2_struct_0(sK1)
% 7.42/1.46      | v2_struct_0(sK0)
% 7.42/1.46      | ~ l1_pre_topc(sK0)
% 7.42/1.46      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_595]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_0,plain,
% 7.42/1.46      ( ~ r1_tarski(X0,X1)
% 7.42/1.46      | ~ r1_tarski(X2,X3)
% 7.42/1.46      | r1_tarski(k2_xboole_0(X2,X0),k2_xboole_0(X3,X1)) ),
% 7.42/1.46      inference(cnf_transformation,[],[f33]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_614,plain,
% 7.42/1.46      ( ~ r1_tarski(X0_44,X1_44)
% 7.42/1.46      | ~ r1_tarski(X2_44,X3_44)
% 7.42/1.46      | r1_tarski(k2_xboole_0(X2_44,X0_44),k2_xboole_0(X3_44,X1_44)) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_0]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1291,plain,
% 7.42/1.46      ( ~ r1_tarski(X0_44,X1_44)
% 7.42/1.46      | r1_tarski(k2_xboole_0(X0_44,u1_struct_0(X0_43)),k2_xboole_0(X1_44,u1_struct_0(X1_43)))
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_614]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1334,plain,
% 7.42/1.46      ( r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X2_43))
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X3_43)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1291]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_14370,plain,
% 7.42/1.46      ( r1_tarski(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1334]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_622,plain,
% 7.42/1.46      ( ~ r1_tarski(X0_44,X1_44)
% 7.42/1.46      | r1_tarski(X2_44,X3_44)
% 7.42/1.46      | X2_44 != X0_44
% 7.42/1.46      | X3_44 != X1_44 ),
% 7.42/1.46      theory(equality) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1528,plain,
% 7.42/1.46      ( r1_tarski(X0_44,X1_44)
% 7.42/1.46      | ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
% 7.42/1.46      | X0_44 != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 7.42/1.46      | X1_44 != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_622]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1945,plain,
% 7.42/1.46      ( ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
% 7.42/1.46      | r1_tarski(u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)),X0_44)
% 7.42/1.46      | X0_44 != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43))
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)) != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1528]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_2673,plain,
% 7.42/1.46      ( ~ r1_tarski(k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)),k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)))
% 7.42/1.46      | r1_tarski(u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)),u1_struct_0(k1_tsep_1(X5_43,X2_43,X3_43)))
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X4_43,X0_43,X1_43)) != k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 7.42/1.46      | u1_struct_0(k1_tsep_1(X5_43,X2_43,X3_43)) != k2_xboole_0(u1_struct_0(X2_43),u1_struct_0(X3_43)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1945]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_7226,plain,
% 7.42/1.46      ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
% 7.42/1.46      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))
% 7.42/1.46      | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 7.42/1.46      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_2673]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_17,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK2,sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f51]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_601,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK2,sK0) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_17]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1053,plain,
% 7.42/1.46      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.42/1.46      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1059,plain,
% 7.42/1.46      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 7.42/1.46      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 7.42/1.46      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 7.42/1.46      | v2_struct_0(X0_43) = iProver_top
% 7.42/1.46      | v2_struct_0(X1_43) = iProver_top
% 7.42/1.46      | v2_struct_0(X2_43) = iProver_top
% 7.42/1.46      | l1_pre_topc(X0_43) != iProver_top ),
% 7.42/1.46      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_3761,plain,
% 7.42/1.46      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 7.42/1.46      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.42/1.46      | v2_struct_0(X0_43) = iProver_top
% 7.42/1.46      | v2_struct_0(sK2) = iProver_top
% 7.42/1.46      | v2_struct_0(sK0) = iProver_top
% 7.42/1.46      | l1_pre_topc(sK0) != iProver_top ),
% 7.42/1.46      inference(superposition,[status(thm)],[c_1053,c_1059]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_23,negated_conjecture,
% 7.42/1.46      ( ~ v2_struct_0(sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f45]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_24,plain,
% 7.42/1.46      ( v2_struct_0(sK0) != iProver_top ),
% 7.42/1.46      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_21,negated_conjecture,
% 7.42/1.46      ( l1_pre_topc(sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f47]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_26,plain,
% 7.42/1.46      ( l1_pre_topc(sK0) = iProver_top ),
% 7.42/1.46      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_18,negated_conjecture,
% 7.42/1.46      ( ~ v2_struct_0(sK2) ),
% 7.42/1.46      inference(cnf_transformation,[],[f50]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_29,plain,
% 7.42/1.46      ( v2_struct_0(sK2) != iProver_top ),
% 7.42/1.46      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_6074,plain,
% 7.42/1.46      ( v2_struct_0(X0_43) = iProver_top
% 7.42/1.46      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.42/1.46      | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
% 7.42/1.46      inference(global_propositional_subsumption,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_3761,c_24,c_26,c_29]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_6075,plain,
% 7.42/1.46      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 7.42/1.46      | m1_pre_topc(X0_43,sK0) != iProver_top
% 7.42/1.46      | v2_struct_0(X0_43) = iProver_top ),
% 7.42/1.46      inference(renaming,[status(thm)],[c_6074]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_6084,plain,
% 7.42/1.46      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 7.42/1.46      | v2_struct_0(sK2) = iProver_top ),
% 7.42/1.46      inference(superposition,[status(thm)],[c_1053,c_6075]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_610,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ m1_pre_topc(X2_43,X1_43)
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 7.42/1.46      | v2_struct_0(X0_43)
% 7.42/1.46      | v2_struct_0(X2_43)
% 7.42/1.46      | v2_struct_0(X1_43)
% 7.42/1.46      | ~ l1_pre_topc(X1_43) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_5]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_4567,plain,
% 7.42/1.46      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK2,sK0)
% 7.42/1.46      | v2_struct_0(sK2)
% 7.42/1.46      | v2_struct_0(sK0)
% 7.42/1.46      | ~ l1_pre_topc(sK0) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_610]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_11,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | m1_pre_topc(X0,X2)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.42/1.46      | ~ v2_pre_topc(X1)
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f43]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_22,negated_conjecture,
% 7.42/1.46      ( v2_pre_topc(sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f46]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_254,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | m1_pre_topc(X0,X2)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | sK0 != X1 ),
% 7.42/1.46      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_255,plain,
% 7.42/1.46      ( m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.42/1.46      | ~ l1_pre_topc(sK0) ),
% 7.42/1.46      inference(unflattening,[status(thm)],[c_254]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_257,plain,
% 7.42/1.46      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | m1_pre_topc(X0,X1) ),
% 7.42/1.46      inference(global_propositional_subsumption,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_255,c_21]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_258,plain,
% 7.42/1.46      ( m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.42/1.46      inference(renaming,[status(thm)],[c_257]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_594,plain,
% 7.42/1.46      ( m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ m1_pre_topc(X0_43,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1_43,sK0)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_258]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_4462,plain,
% 7.42/1.46      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK2))
% 7.42/1.46      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.42/1.46      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_594]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_624,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | m1_pre_topc(X2_43,X3_43)
% 7.42/1.46      | X2_43 != X0_43
% 7.42/1.46      | X3_43 != X1_43 ),
% 7.42/1.46      theory(equality) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1407,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.42/1.46      | k1_tsep_1(sK0,sK1,sK3) != X0_43
% 7.42/1.46      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1_43 ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_624]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1512,plain,
% 7.42/1.46      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.42/1.46      | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43 ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1407]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_2102,plain,
% 7.42/1.46      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK2))
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.42/1.46      | k1_tsep_1(sK0,sK1,sK3) != k1_tsep_1(sK0,sK1,sK3)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1512]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_8,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ v2_pre_topc(X1)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f41]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_298,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(X1)
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 7.42/1.46      | sK0 != X1 ),
% 7.42/1.46      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_299,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | v2_struct_0(sK0)
% 7.42/1.46      | ~ l1_pre_topc(sK0)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.42/1.46      inference(unflattening,[status(thm)],[c_298]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_303,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | v2_struct_0(X0)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.42/1.46      inference(global_propositional_subsumption,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_299,c_23,c_21]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_592,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,sK0)
% 7.42/1.46      | v2_struct_0(X0_43)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_303]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1785,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK2,sK0)
% 7.42/1.46      | v2_struct_0(sK2)
% 7.42/1.46      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_592]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_10,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,X2)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.42/1.46      | ~ v2_pre_topc(X1)
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f44]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_274,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X2,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,X2)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.42/1.46      | ~ l1_pre_topc(X1)
% 7.42/1.46      | sK0 != X1 ),
% 7.42/1.46      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_275,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.42/1.46      | ~ l1_pre_topc(sK0) ),
% 7.42/1.46      inference(unflattening,[status(thm)],[c_274]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_279,plain,
% 7.42/1.46      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X0,X1) ),
% 7.42/1.46      inference(global_propositional_subsumption,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_275,c_21]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_280,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.42/1.46      inference(renaming,[status(thm)],[c_279]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_593,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ m1_pre_topc(X0_43,sK0)
% 7.42/1.46      | ~ m1_pre_topc(X1_43,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_280]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1507,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,sK2)
% 7.42/1.46      | ~ m1_pre_topc(X0_43,sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK2,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_593]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1736,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK2,sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK1,sK2)
% 7.42/1.46      | ~ m1_pre_topc(sK1,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1507]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1733,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK2,sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK3,sK2)
% 7.42/1.46      | ~ m1_pre_topc(sK3,sK0)
% 7.42/1.46      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1507]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_616,plain,( X0_43 = X0_43 ),theory(equality) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1513,plain,
% 7.42/1.46      ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK1,sK3) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_616]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f34]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_613,plain,
% 7.42/1.46      ( ~ m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ l1_pre_topc(X1_43)
% 7.42/1.46      | l1_pre_topc(X0_43) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_1]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1318,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK2,X0_43)
% 7.42/1.46      | ~ l1_pre_topc(X0_43)
% 7.42/1.46      | l1_pre_topc(sK2) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_613]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1320,plain,
% 7.42/1.46      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_1318]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1305,plain,
% 7.42/1.46      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK3,sK0)
% 7.42/1.46      | ~ m1_pre_topc(sK1,sK0)
% 7.42/1.46      | v2_struct_0(sK3)
% 7.42/1.46      | v2_struct_0(sK1)
% 7.42/1.46      | v2_struct_0(sK0)
% 7.42/1.46      | ~ l1_pre_topc(sK0) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_610]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_2,plain,
% 7.42/1.46      ( m1_pre_topc(X0,X1)
% 7.42/1.46      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.42/1.46      | ~ l1_pre_topc(X1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f35]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_612,plain,
% 7.42/1.46      ( m1_pre_topc(X0_43,X1_43)
% 7.42/1.46      | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
% 7.42/1.46      | ~ l1_pre_topc(X1_43) ),
% 7.42/1.46      inference(subtyping,[status(esa)],[c_2]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_1265,plain,
% 7.42/1.46      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.42/1.46      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 7.42/1.46      | ~ l1_pre_topc(sK2) ),
% 7.42/1.46      inference(instantiation,[status(thm)],[c_612]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_12,negated_conjecture,
% 7.42/1.46      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 7.42/1.46      inference(cnf_transformation,[],[f56]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_13,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK3,sK2) ),
% 7.42/1.46      inference(cnf_transformation,[],[f55]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_14,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK1,sK2) ),
% 7.42/1.46      inference(cnf_transformation,[],[f54]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_15,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK3,sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f53]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_16,negated_conjecture,
% 7.42/1.46      ( ~ v2_struct_0(sK3) ),
% 7.42/1.46      inference(cnf_transformation,[],[f52]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_19,negated_conjecture,
% 7.42/1.46      ( m1_pre_topc(sK1,sK0) ),
% 7.42/1.46      inference(cnf_transformation,[],[f49]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(c_20,negated_conjecture,
% 7.42/1.46      ( ~ v2_struct_0(sK1) ),
% 7.42/1.46      inference(cnf_transformation,[],[f48]) ).
% 7.42/1.46  
% 7.42/1.46  cnf(contradiction,plain,
% 7.42/1.46      ( $false ),
% 7.42/1.46      inference(minisat,
% 7.42/1.46                [status(thm)],
% 7.42/1.46                [c_29873,c_14370,c_7226,c_6084,c_4567,c_4462,c_2102,
% 7.42/1.46                 c_1785,c_1736,c_1733,c_1513,c_1320,c_1305,c_1265,c_12,
% 7.42/1.46                 c_13,c_14,c_15,c_16,c_17,c_29,c_18,c_19,c_20,c_21,c_23]) ).
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.42/1.46  
% 7.42/1.46  ------                               Statistics
% 7.42/1.46  
% 7.42/1.46  ------ General
% 7.42/1.46  
% 7.42/1.46  abstr_ref_over_cycles:                  0
% 7.42/1.46  abstr_ref_under_cycles:                 0
% 7.42/1.46  gc_basic_clause_elim:                   0
% 7.42/1.46  forced_gc_time:                         0
% 7.42/1.46  parsing_time:                           0.008
% 7.42/1.46  unif_index_cands_time:                  0.
% 7.42/1.46  unif_index_add_time:                    0.
% 7.42/1.46  orderings_time:                         0.
% 7.42/1.46  out_proof_time:                         0.01
% 7.42/1.46  total_time:                             0.785
% 7.42/1.46  num_of_symbols:                         49
% 7.42/1.46  num_of_terms:                           22980
% 7.42/1.46  
% 7.42/1.46  ------ Preprocessing
% 7.42/1.46  
% 7.42/1.46  num_of_splits:                          0
% 7.42/1.46  num_of_split_atoms:                     0
% 7.42/1.46  num_of_reused_defs:                     0
% 7.42/1.46  num_eq_ax_congr_red:                    3
% 7.42/1.46  num_of_sem_filtered_clauses:            1
% 7.42/1.46  num_of_subtypes:                        3
% 7.42/1.46  monotx_restored_types:                  0
% 7.42/1.46  sat_num_of_epr_types:                   0
% 7.42/1.46  sat_num_of_non_cyclic_types:            0
% 7.42/1.46  sat_guarded_non_collapsed_types:        1
% 7.42/1.46  num_pure_diseq_elim:                    0
% 7.42/1.46  simp_replaced_by:                       0
% 7.42/1.46  res_preprocessed:                       122
% 7.42/1.46  prep_upred:                             0
% 7.42/1.46  prep_unflattend:                        5
% 7.42/1.46  smt_new_axioms:                         0
% 7.42/1.46  pred_elim_cands:                        5
% 7.42/1.46  pred_elim:                              1
% 7.42/1.46  pred_elim_cl:                           1
% 7.42/1.46  pred_elim_cycles:                       3
% 7.42/1.46  merged_defs:                            0
% 7.42/1.46  merged_defs_ncl:                        0
% 7.42/1.46  bin_hyper_res:                          0
% 7.42/1.46  prep_cycles:                            4
% 7.42/1.46  pred_elim_time:                         0.007
% 7.42/1.46  splitting_time:                         0.
% 7.42/1.46  sem_filter_time:                        0.
% 7.42/1.46  monotx_time:                            0.
% 7.42/1.46  subtype_inf_time:                       0.
% 7.42/1.46  
% 7.42/1.46  ------ Problem properties
% 7.42/1.46  
% 7.42/1.46  clauses:                                23
% 7.42/1.46  conjectures:                            11
% 7.42/1.46  epr:                                    12
% 7.42/1.46  horn:                                   17
% 7.42/1.46  ground:                                 11
% 7.42/1.46  unary:                                  11
% 7.42/1.46  binary:                                 1
% 7.42/1.46  lits:                                   72
% 7.42/1.46  lits_eq:                                4
% 7.42/1.46  fd_pure:                                0
% 7.42/1.46  fd_pseudo:                              0
% 7.42/1.46  fd_cond:                                0
% 7.42/1.46  fd_pseudo_cond:                         1
% 7.42/1.46  ac_symbols:                             0
% 7.42/1.46  
% 7.42/1.46  ------ Propositional Solver
% 7.42/1.46  
% 7.42/1.46  prop_solver_calls:                      31
% 7.42/1.46  prop_fast_solver_calls:                 1911
% 7.42/1.46  smt_solver_calls:                       0
% 7.42/1.46  smt_fast_solver_calls:                  0
% 7.42/1.46  prop_num_of_clauses:                    9400
% 7.42/1.46  prop_preprocess_simplified:             12641
% 7.42/1.46  prop_fo_subsumed:                       192
% 7.42/1.46  prop_solver_time:                       0.
% 7.42/1.46  smt_solver_time:                        0.
% 7.42/1.46  smt_fast_solver_time:                   0.
% 7.42/1.46  prop_fast_solver_time:                  0.
% 7.42/1.46  prop_unsat_core_time:                   0.001
% 7.42/1.46  
% 7.42/1.46  ------ QBF
% 7.42/1.46  
% 7.42/1.46  qbf_q_res:                              0
% 7.42/1.46  qbf_num_tautologies:                    0
% 7.42/1.46  qbf_prep_cycles:                        0
% 7.42/1.46  
% 7.42/1.46  ------ BMC1
% 7.42/1.46  
% 7.42/1.46  bmc1_current_bound:                     -1
% 7.42/1.46  bmc1_last_solved_bound:                 -1
% 7.42/1.46  bmc1_unsat_core_size:                   -1
% 7.42/1.46  bmc1_unsat_core_parents_size:           -1
% 7.42/1.46  bmc1_merge_next_fun:                    0
% 7.42/1.46  bmc1_unsat_core_clauses_time:           0.
% 7.42/1.46  
% 7.42/1.46  ------ Instantiation
% 7.42/1.46  
% 7.42/1.46  inst_num_of_clauses:                    2049
% 7.42/1.46  inst_num_in_passive:                    175
% 7.42/1.46  inst_num_in_active:                     1141
% 7.42/1.46  inst_num_in_unprocessed:                732
% 7.42/1.46  inst_num_of_loops:                      1254
% 7.42/1.46  inst_num_of_learning_restarts:          0
% 7.42/1.46  inst_num_moves_active_passive:          108
% 7.42/1.46  inst_lit_activity:                      0
% 7.42/1.46  inst_lit_activity_moves:                1
% 7.42/1.46  inst_num_tautologies:                   0
% 7.42/1.46  inst_num_prop_implied:                  0
% 7.42/1.46  inst_num_existing_simplified:           0
% 7.42/1.46  inst_num_eq_res_simplified:             0
% 7.42/1.46  inst_num_child_elim:                    0
% 7.42/1.46  inst_num_of_dismatching_blockings:      1382
% 7.42/1.46  inst_num_of_non_proper_insts:           3062
% 7.42/1.46  inst_num_of_duplicates:                 0
% 7.42/1.46  inst_inst_num_from_inst_to_res:         0
% 7.42/1.46  inst_dismatching_checking_time:         0.
% 7.42/1.46  
% 7.42/1.46  ------ Resolution
% 7.42/1.46  
% 7.42/1.46  res_num_of_clauses:                     0
% 7.42/1.46  res_num_in_passive:                     0
% 7.42/1.46  res_num_in_active:                      0
% 7.42/1.46  res_num_of_loops:                       126
% 7.42/1.46  res_forward_subset_subsumed:            61
% 7.42/1.46  res_backward_subset_subsumed:           2
% 7.42/1.46  res_forward_subsumed:                   0
% 7.42/1.46  res_backward_subsumed:                  0
% 7.42/1.46  res_forward_subsumption_resolution:     2
% 7.42/1.46  res_backward_subsumption_resolution:    0
% 7.42/1.46  res_clause_to_clause_subsumption:       4863
% 7.42/1.46  res_orphan_elimination:                 0
% 7.42/1.46  res_tautology_del:                      200
% 7.42/1.46  res_num_eq_res_simplified:              0
% 7.42/1.46  res_num_sel_changes:                    0
% 7.42/1.46  res_moves_from_active_to_pass:          0
% 7.42/1.46  
% 7.42/1.46  ------ Superposition
% 7.42/1.46  
% 7.42/1.46  sup_time_total:                         0.
% 7.42/1.46  sup_time_generating:                    0.
% 7.42/1.46  sup_time_sim_full:                      0.
% 7.42/1.46  sup_time_sim_immed:                     0.
% 7.42/1.46  
% 7.42/1.46  sup_num_of_clauses:                     1409
% 7.42/1.46  sup_num_in_active:                      248
% 7.42/1.46  sup_num_in_passive:                     1161
% 7.42/1.46  sup_num_of_loops:                       250
% 7.42/1.46  sup_fw_superposition:                   749
% 7.42/1.46  sup_bw_superposition:                   988
% 7.42/1.46  sup_immediate_simplified:               156
% 7.42/1.46  sup_given_eliminated:                   0
% 7.42/1.46  comparisons_done:                       0
% 7.42/1.46  comparisons_avoided:                    0
% 7.42/1.46  
% 7.42/1.46  ------ Simplifications
% 7.42/1.46  
% 7.42/1.46  
% 7.42/1.46  sim_fw_subset_subsumed:                 28
% 7.42/1.46  sim_bw_subset_subsumed:                 26
% 7.42/1.46  sim_fw_subsumed:                        6
% 7.42/1.46  sim_bw_subsumed:                        10
% 7.42/1.46  sim_fw_subsumption_res:                 1
% 7.42/1.46  sim_bw_subsumption_res:                 0
% 7.42/1.46  sim_tautology_del:                      12
% 7.42/1.46  sim_eq_tautology_del:                   0
% 7.42/1.46  sim_eq_res_simp:                        0
% 7.42/1.46  sim_fw_demodulated:                     8
% 7.42/1.46  sim_bw_demodulated:                     0
% 7.42/1.46  sim_light_normalised:                   98
% 7.42/1.46  sim_joinable_taut:                      0
% 7.42/1.46  sim_joinable_simp:                      0
% 7.42/1.46  sim_ac_normalised:                      0
% 7.42/1.46  sim_smt_subsumption:                    0
% 7.42/1.46  
%------------------------------------------------------------------------------
