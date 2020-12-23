%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:10 EST 2020

% Result     : Theorem 51.83s
% Output     : CNFRefutation 51.83s
% Verified   : 
% Statistics : Number of formulae       :  242 (3740 expanded)
%              Number of clauses        :  186 ( 938 expanded)
%              Number of leaves         :   13 (1300 expanded)
%              Depth                    :   32
%              Number of atoms          : 1365 (37454 expanded)
%              Number of equality atoms :  451 (1308 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f31,f30,f29,f28])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
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
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f25])).

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
    inference(equality_resolution,[],[f34])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tsep_1(X0,X1,X2) = X3
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_533,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_534,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_538,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_23])).

cnf(c_539,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_914,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_539])).

cnf(c_78705,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,X1_43,X2_43),sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,X1_43,X2_43))
    | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X1_43,X2_43),X0_43)) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_78985,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43))
    | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),sK2))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_78705])).

cnf(c_128779,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_78985])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_583,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_584,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_23])).

cnf(c_589,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_912,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_589])).

cnf(c_98104,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
    | m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_115716,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_98104])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_558,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_559,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_23])).

cnf(c_564,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_913,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_564])).

cnf(c_108788,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_929,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1280,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_928,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1281,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_408,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X0,X1)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_409,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_23,c_21])).

cnf(c_412,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_411])).

cnf(c_918,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) = k1_tsep_1(sK0,X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_1291,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X1_43,X0_43)
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_4181,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1291])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_925,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1284,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_387,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_388,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_23,c_21])).

cnf(c_393,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_919,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | v2_struct_0(X0_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_1290,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_2453,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1290])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1411,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_2467,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2453,c_18,c_17,c_1411])).

cnf(c_4187,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4181,c_2467])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_30,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4396,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4187,c_27,c_28,c_29,c_30])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X4,X1)
    | m1_pre_topc(k1_tsep_1(X1,X3,X0),k1_tsep_1(X1,X2,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_342,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X4,X1)
    | m1_pre_topc(k1_tsep_1(X1,X3,X0),k1_tsep_1(X1,X2,X4))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_343,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_347,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_23,c_21])).

cnf(c_348,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_920,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X3_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ m1_pre_topc(X2_43,sK0)
    | ~ m1_pre_topc(X3_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X2_43),k1_tsep_1(sK0,X1_43,X3_43))
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43) ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_1289,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X3_43) != iProver_top
    | m1_pre_topc(X3_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X2_43),k1_tsep_1(sK0,X1_43,X3_43)) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_255,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_xboole_0(X3,X4) = X4
    | u1_struct_0(X0) != X4
    | u1_struct_0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_256,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_460,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ l1_pre_topc(X1)
    | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) = u1_struct_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_256])).

cnf(c_461,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_465,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1)
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_21])).

cnf(c_466,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_916,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_1293,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43)
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_3291,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | m1_pre_topc(X1_43,X3_43) != iProver_top
    | m1_pre_topc(X3_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1293])).

cnf(c_979,plain,
    ( m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_4474,plain,
    ( m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X3_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,X3_43) != iProver_top
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
    | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_979])).

cnf(c_4475,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | m1_pre_topc(X1_43,X3_43) != iProver_top
    | m1_pre_topc(X3_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4474])).

cnf(c_4479,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = u1_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X1_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4396,c_4475])).

cnf(c_923,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1286,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_2,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_136,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_5,c_4,c_3])).

cnf(c_137,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_508,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_21])).

cnf(c_509,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_513,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_23])).

cnf(c_514,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_513])).

cnf(c_915,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_1294,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_3987,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1294])).

cnf(c_4135,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_27])).

cnf(c_4136,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4135])).

cnf(c_4142,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_4136])).

cnf(c_2471,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1293])).

cnf(c_1428,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK0)
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_1609,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_2517,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2471,c_19,c_17,c_14,c_1609])).

cnf(c_4145,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4142,c_2517])).

cnf(c_4381,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4145,c_29])).

cnf(c_4503,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X1_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4479,c_4381,c_4396])).

cnf(c_1368,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_1517,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1518,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1517])).

cnf(c_33957,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4503,c_27,c_28,c_29,c_30,c_1518])).

cnf(c_33958,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X1_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_33957])).

cnf(c_33964,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_33958])).

cnf(c_34007,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33964,c_27,c_28])).

cnf(c_34008,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_34007])).

cnf(c_34013,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_34008])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_927,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1282,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_1297,plain,
    ( m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_3988,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1294])).

cnf(c_977,plain,
    ( m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_5541,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3988,c_977])).

cnf(c_5542,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5541])).

cnf(c_5549,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_5542])).

cnf(c_10033,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5549,c_27])).

cnf(c_10034,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_10033])).

cnf(c_10039,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_10034])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_32,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1514,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1515,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1402,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_1576,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1577,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_2243,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_2267,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_10063,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10039,c_27,c_28,c_31,c_32,c_1515,c_1577,c_2267])).

cnf(c_10064,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_10063])).

cnf(c_10070,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_10064])).

cnf(c_10504,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10070,c_29])).

cnf(c_34016,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34013,c_10504])).

cnf(c_4478,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | m1_pre_topc(X1_43,X3_43) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(X3_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_4475])).

cnf(c_33415,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))) = u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_4478])).

cnf(c_33667,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))) = u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33415,c_27,c_28,c_29,c_30])).

cnf(c_33673,plain,
    ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = u1_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_33667])).

cnf(c_33690,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33673,c_4381,c_4396,c_10504])).

cnf(c_34300,plain,
    ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34016,c_29,c_30,c_31,c_32,c_33690])).

cnf(c_3986,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1294])).

cnf(c_4074,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_29])).

cnf(c_4075,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4074])).

cnf(c_4081,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_4075])).

cnf(c_1439,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1629,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_4104,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4081,c_18,c_17,c_1629])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X0)
    | k1_tsep_1(X1,X3,X2) = X0
    | k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_608,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_pre_topc(X0)
    | k1_tsep_1(X1,X3,X2) = X0
    | k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) != u1_struct_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_609,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(X2)
    | k1_tsep_1(sK0,X0,X1) = X2
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ v1_pre_topc(X2)
    | k1_tsep_1(sK0,X0,X1) = X2
    | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_23])).

cnf(c_614,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X0)
    | k1_tsep_1(sK0,X1,X2) = X0
    | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_613])).

cnf(c_911,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ m1_pre_topc(X2_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X0_43)
    | ~ v1_pre_topc(X0_43)
    | k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43)) != u1_struct_0(X0_43)
    | k1_tsep_1(sK0,X1_43,X2_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_614])).

cnf(c_1298,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) != u1_struct_0(X2_43)
    | k1_tsep_1(sK0,X0_43,X1_43) = X2_43
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v1_pre_topc(X2_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_4302,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
    | k1_tsep_1(sK0,sK2,sK2) = X0_43
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_1298])).

cnf(c_4710,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
    | k1_tsep_1(sK0,sK2,sK2) = X0_43
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4302,c_29,c_30])).

cnf(c_4711,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
    | k1_tsep_1(sK0,sK2,sK2) = X0_43
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_4710])).

cnf(c_4716,plain,
    ( u1_struct_0(X0_43) != u1_struct_0(sK2)
    | k1_tsep_1(sK0,sK2,sK2) = X0_43
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4711,c_4381,c_4396])).

cnf(c_4717,plain,
    ( u1_struct_0(X0_43) != u1_struct_0(sK2)
    | k1_tsep_1(sK0,sK1,sK2) = X0_43
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4716,c_4396])).

cnf(c_34323,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34300,c_4717])).

cnf(c_34350,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
    | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_34323])).

cnf(c_935,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_5657,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != X0_43
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_7269,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != k1_tsep_1(sK0,X0_43,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,X0_43,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_5657])).

cnf(c_19757,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != k1_tsep_1(sK0,sK1,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7269])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_434,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_435,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_437,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_23,c_21])).

cnf(c_438,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_437])).

cnf(c_917,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) != k1_tsep_1(sK0,X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_2240,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) != k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_5133,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_2529,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,sK1,X0_43) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_3342,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_128779,c_115716,c_108788,c_34350,c_19757,c_5133,c_3342,c_1576,c_1514,c_12,c_14,c_15,c_16,c_17,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 51.83/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.83/6.99  
% 51.83/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.83/6.99  
% 51.83/6.99  ------  iProver source info
% 51.83/6.99  
% 51.83/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.83/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.83/6.99  git: non_committed_changes: false
% 51.83/6.99  git: last_make_outside_of_git: false
% 51.83/6.99  
% 51.83/6.99  ------ 
% 51.83/6.99  
% 51.83/6.99  ------ Input Options
% 51.83/6.99  
% 51.83/6.99  --out_options                           all
% 51.83/6.99  --tptp_safe_out                         true
% 51.83/6.99  --problem_path                          ""
% 51.83/6.99  --include_path                          ""
% 51.83/6.99  --clausifier                            res/vclausify_rel
% 51.83/6.99  --clausifier_options                    ""
% 51.83/6.99  --stdin                                 false
% 51.83/6.99  --stats_out                             all
% 51.83/6.99  
% 51.83/6.99  ------ General Options
% 51.83/6.99  
% 51.83/6.99  --fof                                   false
% 51.83/6.99  --time_out_real                         305.
% 51.83/6.99  --time_out_virtual                      -1.
% 51.83/6.99  --symbol_type_check                     false
% 51.83/6.99  --clausify_out                          false
% 51.83/6.99  --sig_cnt_out                           false
% 51.83/6.99  --trig_cnt_out                          false
% 51.83/6.99  --trig_cnt_out_tolerance                1.
% 51.83/6.99  --trig_cnt_out_sk_spl                   false
% 51.83/6.99  --abstr_cl_out                          false
% 51.83/6.99  
% 51.83/6.99  ------ Global Options
% 51.83/6.99  
% 51.83/6.99  --schedule                              default
% 51.83/6.99  --add_important_lit                     false
% 51.83/6.99  --prop_solver_per_cl                    1000
% 51.83/6.99  --min_unsat_core                        false
% 51.83/6.99  --soft_assumptions                      false
% 51.83/6.99  --soft_lemma_size                       3
% 51.83/6.99  --prop_impl_unit_size                   0
% 51.83/6.99  --prop_impl_unit                        []
% 51.83/6.99  --share_sel_clauses                     true
% 51.83/6.99  --reset_solvers                         false
% 51.83/6.99  --bc_imp_inh                            [conj_cone]
% 51.83/6.99  --conj_cone_tolerance                   3.
% 51.83/6.99  --extra_neg_conj                        none
% 51.83/6.99  --large_theory_mode                     true
% 51.83/6.99  --prolific_symb_bound                   200
% 51.83/6.99  --lt_threshold                          2000
% 51.83/6.99  --clause_weak_htbl                      true
% 51.83/6.99  --gc_record_bc_elim                     false
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing Options
% 51.83/6.99  
% 51.83/6.99  --preprocessing_flag                    true
% 51.83/6.99  --time_out_prep_mult                    0.1
% 51.83/6.99  --splitting_mode                        input
% 51.83/6.99  --splitting_grd                         true
% 51.83/6.99  --splitting_cvd                         false
% 51.83/6.99  --splitting_cvd_svl                     false
% 51.83/6.99  --splitting_nvd                         32
% 51.83/6.99  --sub_typing                            true
% 51.83/6.99  --prep_gs_sim                           true
% 51.83/6.99  --prep_unflatten                        true
% 51.83/6.99  --prep_res_sim                          true
% 51.83/6.99  --prep_upred                            true
% 51.83/6.99  --prep_sem_filter                       exhaustive
% 51.83/6.99  --prep_sem_filter_out                   false
% 51.83/6.99  --pred_elim                             true
% 51.83/6.99  --res_sim_input                         true
% 51.83/6.99  --eq_ax_congr_red                       true
% 51.83/6.99  --pure_diseq_elim                       true
% 51.83/6.99  --brand_transform                       false
% 51.83/6.99  --non_eq_to_eq                          false
% 51.83/6.99  --prep_def_merge                        true
% 51.83/6.99  --prep_def_merge_prop_impl              false
% 51.83/6.99  --prep_def_merge_mbd                    true
% 51.83/6.99  --prep_def_merge_tr_red                 false
% 51.83/6.99  --prep_def_merge_tr_cl                  false
% 51.83/6.99  --smt_preprocessing                     true
% 51.83/6.99  --smt_ac_axioms                         fast
% 51.83/6.99  --preprocessed_out                      false
% 51.83/6.99  --preprocessed_stats                    false
% 51.83/6.99  
% 51.83/6.99  ------ Abstraction refinement Options
% 51.83/6.99  
% 51.83/6.99  --abstr_ref                             []
% 51.83/6.99  --abstr_ref_prep                        false
% 51.83/6.99  --abstr_ref_until_sat                   false
% 51.83/6.99  --abstr_ref_sig_restrict                funpre
% 51.83/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.83/6.99  --abstr_ref_under                       []
% 51.83/6.99  
% 51.83/6.99  ------ SAT Options
% 51.83/6.99  
% 51.83/6.99  --sat_mode                              false
% 51.83/6.99  --sat_fm_restart_options                ""
% 51.83/6.99  --sat_gr_def                            false
% 51.83/6.99  --sat_epr_types                         true
% 51.83/6.99  --sat_non_cyclic_types                  false
% 51.83/6.99  --sat_finite_models                     false
% 51.83/6.99  --sat_fm_lemmas                         false
% 51.83/6.99  --sat_fm_prep                           false
% 51.83/6.99  --sat_fm_uc_incr                        true
% 51.83/6.99  --sat_out_model                         small
% 51.83/6.99  --sat_out_clauses                       false
% 51.83/6.99  
% 51.83/6.99  ------ QBF Options
% 51.83/6.99  
% 51.83/6.99  --qbf_mode                              false
% 51.83/6.99  --qbf_elim_univ                         false
% 51.83/6.99  --qbf_dom_inst                          none
% 51.83/6.99  --qbf_dom_pre_inst                      false
% 51.83/6.99  --qbf_sk_in                             false
% 51.83/6.99  --qbf_pred_elim                         true
% 51.83/6.99  --qbf_split                             512
% 51.83/6.99  
% 51.83/6.99  ------ BMC1 Options
% 51.83/6.99  
% 51.83/6.99  --bmc1_incremental                      false
% 51.83/6.99  --bmc1_axioms                           reachable_all
% 51.83/6.99  --bmc1_min_bound                        0
% 51.83/6.99  --bmc1_max_bound                        -1
% 51.83/6.99  --bmc1_max_bound_default                -1
% 51.83/6.99  --bmc1_symbol_reachability              true
% 51.83/6.99  --bmc1_property_lemmas                  false
% 51.83/6.99  --bmc1_k_induction                      false
% 51.83/6.99  --bmc1_non_equiv_states                 false
% 51.83/6.99  --bmc1_deadlock                         false
% 51.83/6.99  --bmc1_ucm                              false
% 51.83/6.99  --bmc1_add_unsat_core                   none
% 51.83/6.99  --bmc1_unsat_core_children              false
% 51.83/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.83/6.99  --bmc1_out_stat                         full
% 51.83/6.99  --bmc1_ground_init                      false
% 51.83/6.99  --bmc1_pre_inst_next_state              false
% 51.83/6.99  --bmc1_pre_inst_state                   false
% 51.83/6.99  --bmc1_pre_inst_reach_state             false
% 51.83/6.99  --bmc1_out_unsat_core                   false
% 51.83/6.99  --bmc1_aig_witness_out                  false
% 51.83/6.99  --bmc1_verbose                          false
% 51.83/6.99  --bmc1_dump_clauses_tptp                false
% 51.83/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.83/6.99  --bmc1_dump_file                        -
% 51.83/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.83/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.83/6.99  --bmc1_ucm_extend_mode                  1
% 51.83/6.99  --bmc1_ucm_init_mode                    2
% 51.83/6.99  --bmc1_ucm_cone_mode                    none
% 51.83/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.83/6.99  --bmc1_ucm_relax_model                  4
% 51.83/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.83/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.83/6.99  --bmc1_ucm_layered_model                none
% 51.83/6.99  --bmc1_ucm_max_lemma_size               10
% 51.83/6.99  
% 51.83/6.99  ------ AIG Options
% 51.83/6.99  
% 51.83/6.99  --aig_mode                              false
% 51.83/6.99  
% 51.83/6.99  ------ Instantiation Options
% 51.83/6.99  
% 51.83/6.99  --instantiation_flag                    true
% 51.83/6.99  --inst_sos_flag                         true
% 51.83/6.99  --inst_sos_phase                        true
% 51.83/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.83/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.83/6.99  --inst_lit_sel_side                     num_symb
% 51.83/6.99  --inst_solver_per_active                1400
% 51.83/6.99  --inst_solver_calls_frac                1.
% 51.83/6.99  --inst_passive_queue_type               priority_queues
% 51.83/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.83/6.99  --inst_passive_queues_freq              [25;2]
% 51.83/6.99  --inst_dismatching                      true
% 51.83/6.99  --inst_eager_unprocessed_to_passive     true
% 51.83/6.99  --inst_prop_sim_given                   true
% 51.83/6.99  --inst_prop_sim_new                     false
% 51.83/6.99  --inst_subs_new                         false
% 51.83/6.99  --inst_eq_res_simp                      false
% 51.83/6.99  --inst_subs_given                       false
% 51.83/6.99  --inst_orphan_elimination               true
% 51.83/6.99  --inst_learning_loop_flag               true
% 51.83/6.99  --inst_learning_start                   3000
% 51.83/6.99  --inst_learning_factor                  2
% 51.83/6.99  --inst_start_prop_sim_after_learn       3
% 51.83/6.99  --inst_sel_renew                        solver
% 51.83/6.99  --inst_lit_activity_flag                true
% 51.83/6.99  --inst_restr_to_given                   false
% 51.83/6.99  --inst_activity_threshold               500
% 51.83/6.99  --inst_out_proof                        true
% 51.83/6.99  
% 51.83/6.99  ------ Resolution Options
% 51.83/6.99  
% 51.83/6.99  --resolution_flag                       true
% 51.83/6.99  --res_lit_sel                           adaptive
% 51.83/6.99  --res_lit_sel_side                      none
% 51.83/6.99  --res_ordering                          kbo
% 51.83/6.99  --res_to_prop_solver                    active
% 51.83/6.99  --res_prop_simpl_new                    false
% 51.83/6.99  --res_prop_simpl_given                  true
% 51.83/6.99  --res_passive_queue_type                priority_queues
% 51.83/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.83/6.99  --res_passive_queues_freq               [15;5]
% 51.83/6.99  --res_forward_subs                      full
% 51.83/6.99  --res_backward_subs                     full
% 51.83/6.99  --res_forward_subs_resolution           true
% 51.83/6.99  --res_backward_subs_resolution          true
% 51.83/6.99  --res_orphan_elimination                true
% 51.83/6.99  --res_time_limit                        2.
% 51.83/6.99  --res_out_proof                         true
% 51.83/6.99  
% 51.83/6.99  ------ Superposition Options
% 51.83/6.99  
% 51.83/6.99  --superposition_flag                    true
% 51.83/6.99  --sup_passive_queue_type                priority_queues
% 51.83/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.83/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.83/6.99  --demod_completeness_check              fast
% 51.83/6.99  --demod_use_ground                      true
% 51.83/6.99  --sup_to_prop_solver                    passive
% 51.83/6.99  --sup_prop_simpl_new                    true
% 51.83/6.99  --sup_prop_simpl_given                  true
% 51.83/6.99  --sup_fun_splitting                     true
% 51.83/6.99  --sup_smt_interval                      50000
% 51.83/6.99  
% 51.83/6.99  ------ Superposition Simplification Setup
% 51.83/6.99  
% 51.83/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.83/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.83/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.83/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.83/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.83/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.83/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.83/6.99  --sup_immed_triv                        [TrivRules]
% 51.83/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_immed_bw_main                     []
% 51.83/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.83/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.83/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_input_bw                          []
% 51.83/6.99  
% 51.83/6.99  ------ Combination Options
% 51.83/6.99  
% 51.83/6.99  --comb_res_mult                         3
% 51.83/6.99  --comb_sup_mult                         2
% 51.83/6.99  --comb_inst_mult                        10
% 51.83/6.99  
% 51.83/6.99  ------ Debug Options
% 51.83/6.99  
% 51.83/6.99  --dbg_backtrace                         false
% 51.83/6.99  --dbg_dump_prop_clauses                 false
% 51.83/6.99  --dbg_dump_prop_clauses_file            -
% 51.83/6.99  --dbg_out_stat                          false
% 51.83/6.99  ------ Parsing...
% 51.83/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.83/6.99  ------ Proving...
% 51.83/6.99  ------ Problem Properties 
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  clauses                                 20
% 51.83/6.99  conjectures                             10
% 51.83/6.99  EPR                                     9
% 51.83/6.99  Horn                                    11
% 51.83/6.99  unary                                   10
% 51.83/6.99  binary                                  0
% 51.83/6.99  lits                                    69
% 51.83/6.99  lits eq                                 7
% 51.83/6.99  fd_pure                                 0
% 51.83/6.99  fd_pseudo                               0
% 51.83/6.99  fd_cond                                 0
% 51.83/6.99  fd_pseudo_cond                          1
% 51.83/6.99  AC symbols                              0
% 51.83/6.99  
% 51.83/6.99  ------ Schedule dynamic 5 is on 
% 51.83/6.99  
% 51.83/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  ------ 
% 51.83/6.99  Current options:
% 51.83/6.99  ------ 
% 51.83/6.99  
% 51.83/6.99  ------ Input Options
% 51.83/6.99  
% 51.83/6.99  --out_options                           all
% 51.83/6.99  --tptp_safe_out                         true
% 51.83/6.99  --problem_path                          ""
% 51.83/6.99  --include_path                          ""
% 51.83/6.99  --clausifier                            res/vclausify_rel
% 51.83/6.99  --clausifier_options                    ""
% 51.83/6.99  --stdin                                 false
% 51.83/6.99  --stats_out                             all
% 51.83/6.99  
% 51.83/6.99  ------ General Options
% 51.83/6.99  
% 51.83/6.99  --fof                                   false
% 51.83/6.99  --time_out_real                         305.
% 51.83/6.99  --time_out_virtual                      -1.
% 51.83/6.99  --symbol_type_check                     false
% 51.83/6.99  --clausify_out                          false
% 51.83/6.99  --sig_cnt_out                           false
% 51.83/6.99  --trig_cnt_out                          false
% 51.83/6.99  --trig_cnt_out_tolerance                1.
% 51.83/6.99  --trig_cnt_out_sk_spl                   false
% 51.83/6.99  --abstr_cl_out                          false
% 51.83/6.99  
% 51.83/6.99  ------ Global Options
% 51.83/6.99  
% 51.83/6.99  --schedule                              default
% 51.83/6.99  --add_important_lit                     false
% 51.83/6.99  --prop_solver_per_cl                    1000
% 51.83/6.99  --min_unsat_core                        false
% 51.83/6.99  --soft_assumptions                      false
% 51.83/6.99  --soft_lemma_size                       3
% 51.83/6.99  --prop_impl_unit_size                   0
% 51.83/6.99  --prop_impl_unit                        []
% 51.83/6.99  --share_sel_clauses                     true
% 51.83/6.99  --reset_solvers                         false
% 51.83/6.99  --bc_imp_inh                            [conj_cone]
% 51.83/6.99  --conj_cone_tolerance                   3.
% 51.83/6.99  --extra_neg_conj                        none
% 51.83/6.99  --large_theory_mode                     true
% 51.83/6.99  --prolific_symb_bound                   200
% 51.83/6.99  --lt_threshold                          2000
% 51.83/6.99  --clause_weak_htbl                      true
% 51.83/6.99  --gc_record_bc_elim                     false
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing Options
% 51.83/6.99  
% 51.83/6.99  --preprocessing_flag                    true
% 51.83/6.99  --time_out_prep_mult                    0.1
% 51.83/6.99  --splitting_mode                        input
% 51.83/6.99  --splitting_grd                         true
% 51.83/6.99  --splitting_cvd                         false
% 51.83/6.99  --splitting_cvd_svl                     false
% 51.83/6.99  --splitting_nvd                         32
% 51.83/6.99  --sub_typing                            true
% 51.83/6.99  --prep_gs_sim                           true
% 51.83/6.99  --prep_unflatten                        true
% 51.83/6.99  --prep_res_sim                          true
% 51.83/6.99  --prep_upred                            true
% 51.83/6.99  --prep_sem_filter                       exhaustive
% 51.83/6.99  --prep_sem_filter_out                   false
% 51.83/6.99  --pred_elim                             true
% 51.83/6.99  --res_sim_input                         true
% 51.83/6.99  --eq_ax_congr_red                       true
% 51.83/6.99  --pure_diseq_elim                       true
% 51.83/6.99  --brand_transform                       false
% 51.83/6.99  --non_eq_to_eq                          false
% 51.83/6.99  --prep_def_merge                        true
% 51.83/6.99  --prep_def_merge_prop_impl              false
% 51.83/6.99  --prep_def_merge_mbd                    true
% 51.83/6.99  --prep_def_merge_tr_red                 false
% 51.83/6.99  --prep_def_merge_tr_cl                  false
% 51.83/6.99  --smt_preprocessing                     true
% 51.83/6.99  --smt_ac_axioms                         fast
% 51.83/6.99  --preprocessed_out                      false
% 51.83/6.99  --preprocessed_stats                    false
% 51.83/6.99  
% 51.83/6.99  ------ Abstraction refinement Options
% 51.83/6.99  
% 51.83/6.99  --abstr_ref                             []
% 51.83/6.99  --abstr_ref_prep                        false
% 51.83/6.99  --abstr_ref_until_sat                   false
% 51.83/6.99  --abstr_ref_sig_restrict                funpre
% 51.83/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.83/6.99  --abstr_ref_under                       []
% 51.83/6.99  
% 51.83/6.99  ------ SAT Options
% 51.83/6.99  
% 51.83/6.99  --sat_mode                              false
% 51.83/6.99  --sat_fm_restart_options                ""
% 51.83/6.99  --sat_gr_def                            false
% 51.83/6.99  --sat_epr_types                         true
% 51.83/6.99  --sat_non_cyclic_types                  false
% 51.83/6.99  --sat_finite_models                     false
% 51.83/6.99  --sat_fm_lemmas                         false
% 51.83/6.99  --sat_fm_prep                           false
% 51.83/6.99  --sat_fm_uc_incr                        true
% 51.83/6.99  --sat_out_model                         small
% 51.83/6.99  --sat_out_clauses                       false
% 51.83/6.99  
% 51.83/6.99  ------ QBF Options
% 51.83/6.99  
% 51.83/6.99  --qbf_mode                              false
% 51.83/6.99  --qbf_elim_univ                         false
% 51.83/6.99  --qbf_dom_inst                          none
% 51.83/6.99  --qbf_dom_pre_inst                      false
% 51.83/6.99  --qbf_sk_in                             false
% 51.83/6.99  --qbf_pred_elim                         true
% 51.83/6.99  --qbf_split                             512
% 51.83/6.99  
% 51.83/6.99  ------ BMC1 Options
% 51.83/6.99  
% 51.83/6.99  --bmc1_incremental                      false
% 51.83/6.99  --bmc1_axioms                           reachable_all
% 51.83/6.99  --bmc1_min_bound                        0
% 51.83/6.99  --bmc1_max_bound                        -1
% 51.83/6.99  --bmc1_max_bound_default                -1
% 51.83/6.99  --bmc1_symbol_reachability              true
% 51.83/6.99  --bmc1_property_lemmas                  false
% 51.83/6.99  --bmc1_k_induction                      false
% 51.83/6.99  --bmc1_non_equiv_states                 false
% 51.83/6.99  --bmc1_deadlock                         false
% 51.83/6.99  --bmc1_ucm                              false
% 51.83/6.99  --bmc1_add_unsat_core                   none
% 51.83/6.99  --bmc1_unsat_core_children              false
% 51.83/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.83/6.99  --bmc1_out_stat                         full
% 51.83/6.99  --bmc1_ground_init                      false
% 51.83/6.99  --bmc1_pre_inst_next_state              false
% 51.83/6.99  --bmc1_pre_inst_state                   false
% 51.83/6.99  --bmc1_pre_inst_reach_state             false
% 51.83/6.99  --bmc1_out_unsat_core                   false
% 51.83/6.99  --bmc1_aig_witness_out                  false
% 51.83/6.99  --bmc1_verbose                          false
% 51.83/6.99  --bmc1_dump_clauses_tptp                false
% 51.83/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.83/6.99  --bmc1_dump_file                        -
% 51.83/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.83/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.83/6.99  --bmc1_ucm_extend_mode                  1
% 51.83/6.99  --bmc1_ucm_init_mode                    2
% 51.83/6.99  --bmc1_ucm_cone_mode                    none
% 51.83/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.83/6.99  --bmc1_ucm_relax_model                  4
% 51.83/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.83/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.83/6.99  --bmc1_ucm_layered_model                none
% 51.83/6.99  --bmc1_ucm_max_lemma_size               10
% 51.83/6.99  
% 51.83/6.99  ------ AIG Options
% 51.83/6.99  
% 51.83/6.99  --aig_mode                              false
% 51.83/6.99  
% 51.83/6.99  ------ Instantiation Options
% 51.83/6.99  
% 51.83/6.99  --instantiation_flag                    true
% 51.83/6.99  --inst_sos_flag                         true
% 51.83/6.99  --inst_sos_phase                        true
% 51.83/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.83/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.83/6.99  --inst_lit_sel_side                     none
% 51.83/6.99  --inst_solver_per_active                1400
% 51.83/6.99  --inst_solver_calls_frac                1.
% 51.83/6.99  --inst_passive_queue_type               priority_queues
% 51.83/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.83/6.99  --inst_passive_queues_freq              [25;2]
% 51.83/6.99  --inst_dismatching                      true
% 51.83/6.99  --inst_eager_unprocessed_to_passive     true
% 51.83/6.99  --inst_prop_sim_given                   true
% 51.83/6.99  --inst_prop_sim_new                     false
% 51.83/6.99  --inst_subs_new                         false
% 51.83/6.99  --inst_eq_res_simp                      false
% 51.83/6.99  --inst_subs_given                       false
% 51.83/6.99  --inst_orphan_elimination               true
% 51.83/6.99  --inst_learning_loop_flag               true
% 51.83/6.99  --inst_learning_start                   3000
% 51.83/6.99  --inst_learning_factor                  2
% 51.83/6.99  --inst_start_prop_sim_after_learn       3
% 51.83/6.99  --inst_sel_renew                        solver
% 51.83/6.99  --inst_lit_activity_flag                true
% 51.83/6.99  --inst_restr_to_given                   false
% 51.83/6.99  --inst_activity_threshold               500
% 51.83/6.99  --inst_out_proof                        true
% 51.83/6.99  
% 51.83/6.99  ------ Resolution Options
% 51.83/6.99  
% 51.83/6.99  --resolution_flag                       false
% 51.83/6.99  --res_lit_sel                           adaptive
% 51.83/6.99  --res_lit_sel_side                      none
% 51.83/6.99  --res_ordering                          kbo
% 51.83/6.99  --res_to_prop_solver                    active
% 51.83/6.99  --res_prop_simpl_new                    false
% 51.83/6.99  --res_prop_simpl_given                  true
% 51.83/6.99  --res_passive_queue_type                priority_queues
% 51.83/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.83/6.99  --res_passive_queues_freq               [15;5]
% 51.83/6.99  --res_forward_subs                      full
% 51.83/6.99  --res_backward_subs                     full
% 51.83/6.99  --res_forward_subs_resolution           true
% 51.83/6.99  --res_backward_subs_resolution          true
% 51.83/6.99  --res_orphan_elimination                true
% 51.83/6.99  --res_time_limit                        2.
% 51.83/6.99  --res_out_proof                         true
% 51.83/6.99  
% 51.83/6.99  ------ Superposition Options
% 51.83/6.99  
% 51.83/6.99  --superposition_flag                    true
% 51.83/6.99  --sup_passive_queue_type                priority_queues
% 51.83/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.83/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.83/6.99  --demod_completeness_check              fast
% 51.83/6.99  --demod_use_ground                      true
% 51.83/6.99  --sup_to_prop_solver                    passive
% 51.83/6.99  --sup_prop_simpl_new                    true
% 51.83/6.99  --sup_prop_simpl_given                  true
% 51.83/6.99  --sup_fun_splitting                     true
% 51.83/6.99  --sup_smt_interval                      50000
% 51.83/6.99  
% 51.83/6.99  ------ Superposition Simplification Setup
% 51.83/6.99  
% 51.83/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.83/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.83/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.83/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.83/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.83/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.83/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.83/6.99  --sup_immed_triv                        [TrivRules]
% 51.83/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_immed_bw_main                     []
% 51.83/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.83/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.83/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.83/6.99  --sup_input_bw                          []
% 51.83/6.99  
% 51.83/6.99  ------ Combination Options
% 51.83/6.99  
% 51.83/6.99  --comb_res_mult                         3
% 51.83/6.99  --comb_sup_mult                         2
% 51.83/6.99  --comb_inst_mult                        10
% 51.83/6.99  
% 51.83/6.99  ------ Debug Options
% 51.83/6.99  
% 51.83/6.99  --dbg_backtrace                         false
% 51.83/6.99  --dbg_dump_prop_clauses                 false
% 51.83/6.99  --dbg_dump_prop_clauses_file            -
% 51.83/6.99  --dbg_out_stat                          false
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  ------ Proving...
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  % SZS status Theorem for theBenchmark.p
% 51.83/6.99  
% 51.83/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.83/6.99  
% 51.83/6.99  fof(f3,axiom,(
% 51.83/6.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f13,plain,(
% 51.83/6.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f3])).
% 51.83/6.99  
% 51.83/6.99  fof(f14,plain,(
% 51.83/6.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f13])).
% 51.83/6.99  
% 51.83/6.99  fof(f36,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f14])).
% 51.83/6.99  
% 51.83/6.99  fof(f8,conjecture,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f9,negated_conjecture,(
% 51.83/6.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 51.83/6.99    inference(negated_conjecture,[],[f8])).
% 51.83/6.99  
% 51.83/6.99  fof(f23,plain,(
% 51.83/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f9])).
% 51.83/6.99  
% 51.83/6.99  fof(f24,plain,(
% 51.83/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f23])).
% 51.83/6.99  
% 51.83/6.99  fof(f31,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 51.83/6.99    introduced(choice_axiom,[])).
% 51.83/6.99  
% 51.83/6.99  fof(f30,plain,(
% 51.83/6.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 51.83/6.99    introduced(choice_axiom,[])).
% 51.83/6.99  
% 51.83/6.99  fof(f29,plain,(
% 51.83/6.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 51.83/6.99    introduced(choice_axiom,[])).
% 51.83/6.99  
% 51.83/6.99  fof(f28,plain,(
% 51.83/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 51.83/6.99    introduced(choice_axiom,[])).
% 51.83/6.99  
% 51.83/6.99  fof(f32,plain,(
% 51.83/6.99    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 51.83/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f31,f30,f29,f28])).
% 51.83/6.99  
% 51.83/6.99  fof(f47,plain,(
% 51.83/6.99    l1_pre_topc(sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f45,plain,(
% 51.83/6.99    ~v2_struct_0(sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f38,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f14])).
% 51.83/6.99  
% 51.83/6.99  fof(f37,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f14])).
% 51.83/6.99  
% 51.83/6.99  fof(f55,plain,(
% 51.83/6.99    m1_pre_topc(sK3,sK2)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f54,plain,(
% 51.83/6.99    m1_pre_topc(sK1,sK2)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f4,axiom,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f15,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f4])).
% 51.83/6.99  
% 51.83/6.99  fof(f16,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f15])).
% 51.83/6.99  
% 51.83/6.99  fof(f26,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(nnf_transformation,[],[f16])).
% 51.83/6.99  
% 51.83/6.99  fof(f39,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f26])).
% 51.83/6.99  
% 51.83/6.99  fof(f46,plain,(
% 51.83/6.99    v2_pre_topc(sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f51,plain,(
% 51.83/6.99    m1_pre_topc(sK2,sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f5,axiom,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f17,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f5])).
% 51.83/6.99  
% 51.83/6.99  fof(f18,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f17])).
% 51.83/6.99  
% 51.83/6.99  fof(f41,plain,(
% 51.83/6.99    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f18])).
% 51.83/6.99  
% 51.83/6.99  fof(f50,plain,(
% 51.83/6.99    ~v2_struct_0(sK2)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f48,plain,(
% 51.83/6.99    ~v2_struct_0(sK1)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f49,plain,(
% 51.83/6.99    m1_pre_topc(sK1,sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f6,axiom,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f19,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f6])).
% 51.83/6.99  
% 51.83/6.99  fof(f20,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f19])).
% 51.83/6.99  
% 51.83/6.99  fof(f42,plain,(
% 51.83/6.99    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f20])).
% 51.83/6.99  
% 51.83/6.99  fof(f1,axiom,(
% 51.83/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f10,plain,(
% 51.83/6.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.83/6.99    inference(ennf_transformation,[],[f1])).
% 51.83/6.99  
% 51.83/6.99  fof(f33,plain,(
% 51.83/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f10])).
% 51.83/6.99  
% 51.83/6.99  fof(f7,axiom,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f21,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f7])).
% 51.83/6.99  
% 51.83/6.99  fof(f22,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.83/6.99    inference(flattening,[],[f21])).
% 51.83/6.99  
% 51.83/6.99  fof(f27,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.83/6.99    inference(nnf_transformation,[],[f22])).
% 51.83/6.99  
% 51.83/6.99  fof(f44,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f27])).
% 51.83/6.99  
% 51.83/6.99  fof(f2,axiom,(
% 51.83/6.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 51.83/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.83/6.99  
% 51.83/6.99  fof(f11,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.83/6.99    inference(ennf_transformation,[],[f2])).
% 51.83/6.99  
% 51.83/6.99  fof(f12,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(flattening,[],[f11])).
% 51.83/6.99  
% 51.83/6.99  fof(f25,plain,(
% 51.83/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.83/6.99    inference(nnf_transformation,[],[f12])).
% 51.83/6.99  
% 51.83/6.99  fof(f34,plain,(
% 51.83/6.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f25])).
% 51.83/6.99  
% 51.83/6.99  fof(f57,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(equality_resolution,[],[f34])).
% 51.83/6.99  
% 51.83/6.99  fof(f53,plain,(
% 51.83/6.99    m1_pre_topc(sK3,sK0)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f52,plain,(
% 51.83/6.99    ~v2_struct_0(sK3)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  fof(f35,plain,(
% 51.83/6.99    ( ! [X2,X0,X3,X1] : (k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f25])).
% 51.83/6.99  
% 51.83/6.99  fof(f40,plain,(
% 51.83/6.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.83/6.99    inference(cnf_transformation,[],[f26])).
% 51.83/6.99  
% 51.83/6.99  fof(f56,plain,(
% 51.83/6.99    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 51.83/6.99    inference(cnf_transformation,[],[f32])).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 51.83/6.99      inference(cnf_transformation,[],[f36]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_21,negated_conjecture,
% 51.83/6.99      ( l1_pre_topc(sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f47]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_533,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_534,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 51.83/6.99      | v2_struct_0(sK0) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_533]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_23,negated_conjecture,
% 51.83/6.99      ( ~ v2_struct_0(sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f45]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_538,plain,
% 51.83/6.99      ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_534,c_23]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_539,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_538]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_914,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_539]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_78705,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(sK0,X1_43,X2_43),sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,X1_43,X2_43))
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X1_43,X2_43),X0_43)) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_914]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_78985,plain,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43))
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),sK2))
% 51.83/6.99      | v2_struct_0(sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_78705]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_128779,plain,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | v2_struct_0(sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_78985]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f38]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_583,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_584,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_583]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_588,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_584,c_23]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_589,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_588]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_912,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_589]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_98104,plain,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),sK2),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43))
% 51.83/6.99      | v2_struct_0(sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_912]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_115716,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | v2_struct_0(sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_98104]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
% 51.83/6.99      inference(cnf_transformation,[],[f37]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_558,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_559,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_558]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_563,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_559,c_23]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_564,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_563]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_913,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43)) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_564]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_108788,plain,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_913]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_13,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK3,sK2) ),
% 51.83/6.99      inference(cnf_transformation,[],[f55]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_929,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK3,sK2) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_13]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1280,plain,
% 51.83/6.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_14,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK1,sK2) ),
% 51.83/6.99      inference(cnf_transformation,[],[f54]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_928,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK1,sK2) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_14]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1281,plain,
% 51.83/6.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_7,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X0)
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f39]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_22,negated_conjecture,
% 51.83/6.99      ( v2_pre_topc(sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f46]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_408,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X1,X2)
% 51.83/6.99      | ~ m1_pre_topc(X0,X2)
% 51.83/6.99      | ~ l1_pre_topc(X2)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X0,X1)
% 51.83/6.99      | sK0 != X2 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_409,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ l1_pre_topc(sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_408]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_411,plain,
% 51.83/6.99      ( v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_409,c_23,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_412,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_411]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_918,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 51.83/6.99      | ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) = k1_tsep_1(sK0,X0_43,X1_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_412]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1291,plain,
% 51.83/6.99      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X1_43,X0_43)
% 51.83/6.99      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4181,plain,
% 51.83/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1281,c_1291]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_17,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK2,sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f51]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_925,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK2,sK0) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_17]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1284,plain,
% 51.83/6.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_8,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f41]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_387,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_388,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ l1_pre_topc(sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_387]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_392,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_388,c_23,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_393,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_392]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_919,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_393]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1290,plain,
% 51.83/6.99      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,X0_43,X0_43)
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2453,plain,
% 51.83/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1284,c_1290]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_18,negated_conjecture,
% 51.83/6.99      ( ~ v2_struct_0(sK2) ),
% 51.83/6.99      inference(cnf_transformation,[],[f50]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1411,plain,
% 51.83/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_919]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2467,plain,
% 51.83/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_2453,c_18,c_17,c_1411]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4187,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(demodulation,[status(thm)],[c_4181,c_2467]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_20,negated_conjecture,
% 51.83/6.99      ( ~ v2_struct_0(sK1) ),
% 51.83/6.99      inference(cnf_transformation,[],[f48]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_27,plain,
% 51.83/6.99      ( v2_struct_0(sK1) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_19,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK1,sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f49]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_28,plain,
% 51.83/6.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_29,plain,
% 51.83/6.99      ( v2_struct_0(sK2) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_30,plain,
% 51.83/6.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4396,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_4187,c_27,c_28,c_29,c_30]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_9,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X2)
% 51.83/6.99      | ~ m1_pre_topc(X0,X4)
% 51.83/6.99      | ~ m1_pre_topc(X4,X1)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(X1,X3,X0),k1_tsep_1(X1,X2,X4))
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X3)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X4) ),
% 51.83/6.99      inference(cnf_transformation,[],[f42]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_342,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X2)
% 51.83/6.99      | ~ m1_pre_topc(X0,X4)
% 51.83/6.99      | ~ m1_pre_topc(X4,X1)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(X1,X3,X0),k1_tsep_1(X1,X2,X4))
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X3)
% 51.83/6.99      | v2_struct_0(X4)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_343,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X3)
% 51.83/6.99      | ~ m1_pre_topc(X3,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3))
% 51.83/6.99      | ~ l1_pre_topc(sK0)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X3)
% 51.83/6.99      | v2_struct_0(sK0) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_342]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_347,plain,
% 51.83/6.99      ( v2_struct_0(X3)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X3)
% 51.83/6.99      | ~ m1_pre_topc(X3,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_343,c_23,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_348,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X3)
% 51.83/6.99      | ~ m1_pre_topc(X3,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X2),k1_tsep_1(sK0,X1,X3))
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X3) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_347]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_920,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 51.83/6.99      | ~ m1_pre_topc(X2_43,X3_43)
% 51.83/6.99      | ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X3_43,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X2_43),k1_tsep_1(sK0,X1_43,X3_43))
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X2_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(X3_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_348]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1289,plain,
% 51.83/6.99      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,X3_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X3_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X2_43),k1_tsep_1(sK0,X1_43,X3_43)) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X3_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_0,plain,
% 51.83/6.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.83/6.99      inference(cnf_transformation,[],[f33]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X0)
% 51.83/6.99      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1) ),
% 51.83/6.99      inference(cnf_transformation,[],[f44]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_255,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X0)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | k2_xboole_0(X3,X4) = X4
% 51.83/6.99      | u1_struct_0(X0) != X4
% 51.83/6.99      | u1_struct_0(X2) != X3 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_256,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X1,X2)
% 51.83/6.99      | ~ m1_pre_topc(X0,X2)
% 51.83/6.99      | ~ v2_pre_topc(X2)
% 51.83/6.99      | ~ l1_pre_topc(X2)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_255]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_460,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X0)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) = u1_struct_0(X0)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_22,c_256]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_461,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ l1_pre_topc(sK0)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_460]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_465,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_461,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_466,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X1) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_465]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_916,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 51.83/6.99      | ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_466]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1293,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43)
% 51.83/6.99      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3291,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
% 51.83/6.99      | m1_pre_topc(X0_43,X2_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,X3_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X3_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X3_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1289,c_1293]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_979,plain,
% 51.83/6.99      ( m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4474,plain,
% 51.83/6.99      ( m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X3_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,X3_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,X2_43) != iProver_top
% 51.83/6.99      | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X3_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_3291,c_979]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4475,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
% 51.83/6.99      | m1_pre_topc(X0_43,X2_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,X3_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X3_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X2_43,X3_43),sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X3_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_4474]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4479,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = u1_struct_0(k1_tsep_1(sK0,sK2,sK2))
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_4396,c_4475]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_923,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK1,sK0) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_19]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1286,plain,
% 51.83/6.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 51.83/6.99      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 51.83/6.99      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 51.83/6.99      inference(cnf_transformation,[],[f57]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_136,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_2,c_5,c_4,c_3]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_137,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_136]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_508,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_137,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_509,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_508]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_513,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_509,c_23]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_514,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_513]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_915,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_514]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1294,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3987,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1286,c_1294]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4135,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_3987,c_27]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4136,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_4135]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4142,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1284,c_4136]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2471,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1281,c_1293]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1428,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,X0_43)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(X0_43) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_916]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1609,plain,
% 51.83/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK2)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_1428]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2517,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_2471,c_19,c_17,c_14,c_1609]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4145,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(light_normalisation,[status(thm)],[c_4142,c_2517]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4381,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_4145,c_29]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4503,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(light_normalisation,[status(thm)],[c_4479,c_4381,c_4396]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1368,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(sK1) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_912]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1517,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | v2_struct_0(sK1) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1518,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_1517]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33957,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_4503,c_27,c_28,c_29,c_30,c_1518]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33958,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_33957]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33964,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1281,c_33958]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34007,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_33964,c_27,c_28]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34008,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_34007]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34013,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1280,c_34008]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_15,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK3,sK0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f53]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_927,negated_conjecture,
% 51.83/6.99      ( m1_pre_topc(sK3,sK0) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_15]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1282,plain,
% 51.83/6.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1297,plain,
% 51.83/6.99      ( m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,X1_43),sK0) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3988,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1297,c_1294]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_977,plain,
% 51.83/6.99      ( m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,X0_43,X1_43)) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5541,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_3988,c_977]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5542,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,X0_43,X1_43),X2_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(X2_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_5541]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5549,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1286,c_5542]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10033,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_5549,c_27]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10034,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,X0_43),X1_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(X1_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_10033]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10039,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1282,c_10034]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_16,negated_conjecture,
% 51.83/6.99      ( ~ v2_struct_0(sK3) ),
% 51.83/6.99      inference(cnf_transformation,[],[f52]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_31,plain,
% 51.83/6.99      ( v2_struct_0(sK3) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_32,plain,
% 51.83/6.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1514,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK3,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(sK3)
% 51.83/6.99      | v2_struct_0(sK1) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1515,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 51.83/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1402,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 51.83/6.99      | v2_struct_0(sK1) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_914]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1576,plain,
% 51.83/6.99      ( ~ m1_pre_topc(sK3,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | v2_struct_0(sK3)
% 51.83/6.99      | v2_struct_0(sK1) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1577,plain,
% 51.83/6.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_1576]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2243,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_915]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2267,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_2243]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10063,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_10039,c_27,c_28,c_31,c_32,c_1515,c_1577,c_2267]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10064,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_10063]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10070,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1284,c_10064]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_10504,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_10070,c_29]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34016,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top ),
% 51.83/6.99      inference(demodulation,[status(thm)],[c_34013,c_10504]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4478,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,X0_43,X1_43)),u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))) = u1_struct_0(k1_tsep_1(sK0,X2_43,X3_43))
% 51.83/6.99      | m1_pre_topc(X0_43,X2_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,X3_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X3_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X3_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1297,c_4475]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33415,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))) = u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))
% 51.83/6.99      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1281,c_4478]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33667,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)),u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))) = u1_struct_0(k1_tsep_1(sK0,sK2,X1_43))
% 51.83/6.99      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_33415,c_27,c_28,c_29,c_30]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33673,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = u1_struct_0(k1_tsep_1(sK0,sK2,sK2))
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1280,c_33667]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_33690,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2)
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v2_struct_0(sK3) = iProver_top ),
% 51.83/6.99      inference(light_normalisation,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_33673,c_4381,c_4396,c_10504]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34300,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = u1_struct_0(sK2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_34016,c_29,c_30,c_31,c_32,c_33690]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3986,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1284,c_1294]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4074,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_3986,c_29]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4075,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_4074]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4081,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_1284,c_4075]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1439,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_915]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1629,plain,
% 51.83/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4104,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_4081,c_18,c_17,c_1629]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X3)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | ~ v1_pre_topc(X0)
% 51.83/6.99      | k1_tsep_1(X1,X3,X2) = X0
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) != u1_struct_0(X0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f35]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_608,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | ~ m1_pre_topc(X3,X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X3)
% 51.83/6.99      | ~ v1_pre_topc(X0)
% 51.83/6.99      | k1_tsep_1(X1,X3,X2) = X0
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) != u1_struct_0(X0)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_609,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | ~ v1_pre_topc(X2)
% 51.83/6.99      | k1_tsep_1(sK0,X0,X1) = X2
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X2) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_608]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_613,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ v1_pre_topc(X2)
% 51.83/6.99      | k1_tsep_1(sK0,X0,X1) = X2
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != u1_struct_0(X2) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_609,c_23]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_614,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2,sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | ~ v1_pre_topc(X0)
% 51.83/6.99      | k1_tsep_1(sK0,X1,X2) = X0
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X0) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_613]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_911,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X2_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X2_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | ~ v1_pre_topc(X0_43)
% 51.83/6.99      | k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43)) != u1_struct_0(X0_43)
% 51.83/6.99      | k1_tsep_1(sK0,X1_43,X2_43) = X0_43 ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_614]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_1298,plain,
% 51.83/6.99      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) != u1_struct_0(X2_43)
% 51.83/6.99      | k1_tsep_1(sK0,X0_43,X1_43) = X2_43
% 51.83/6.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X1_43) = iProver_top
% 51.83/6.99      | v2_struct_0(X2_43) = iProver_top
% 51.83/6.99      | v1_pre_topc(X2_43) != iProver_top ),
% 51.83/6.99      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4302,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
% 51.83/6.99      | k1_tsep_1(sK0,sK2,sK2) = X0_43
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v2_struct_0(sK2) = iProver_top
% 51.83/6.99      | v1_pre_topc(X0_43) != iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_4104,c_1298]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4710,plain,
% 51.83/6.99      ( v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
% 51.83/6.99      | k1_tsep_1(sK0,sK2,sK2) = X0_43
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v1_pre_topc(X0_43) != iProver_top ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_4302,c_29,c_30]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4711,plain,
% 51.83/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) != u1_struct_0(X0_43)
% 51.83/6.99      | k1_tsep_1(sK0,sK2,sK2) = X0_43
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v1_pre_topc(X0_43) != iProver_top ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_4710]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4716,plain,
% 51.83/6.99      ( u1_struct_0(X0_43) != u1_struct_0(sK2)
% 51.83/6.99      | k1_tsep_1(sK0,sK2,sK2) = X0_43
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v1_pre_topc(X0_43) != iProver_top ),
% 51.83/6.99      inference(light_normalisation,[status(thm)],[c_4711,c_4381,c_4396]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_4717,plain,
% 51.83/6.99      ( u1_struct_0(X0_43) != u1_struct_0(sK2)
% 51.83/6.99      | k1_tsep_1(sK0,sK1,sK2) = X0_43
% 51.83/6.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(X0_43) = iProver_top
% 51.83/6.99      | v1_pre_topc(X0_43) != iProver_top ),
% 51.83/6.99      inference(demodulation,[status(thm)],[c_4716,c_4396]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34323,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK1,sK2)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0) != iProver_top
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) = iProver_top
% 51.83/6.99      | v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)) != iProver_top ),
% 51.83/6.99      inference(superposition,[status(thm)],[c_34300,c_4717]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_34350,plain,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2),sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
% 51.83/6.99      | ~ v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2))
% 51.83/6.99      | k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.83/6.99      inference(predicate_to_equality_rev,[status(thm)],[c_34323]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_935,plain,
% 51.83/6.99      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 51.83/6.99      theory(equality) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5657,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != X0_43
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_43
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_935]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_7269,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != k1_tsep_1(sK0,X0_43,sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,X0_43,sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_5657]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_19757,plain,
% 51.83/6.99      ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) != k1_tsep_1(sK0,sK1,sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK1,sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_7269]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_6,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | m1_pre_topc(X2,X0)
% 51.83/6.99      | ~ v2_pre_topc(X1)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0) ),
% 51.83/6.99      inference(cnf_transformation,[],[f40]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_434,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X2,X1)
% 51.83/6.99      | m1_pre_topc(X2,X0)
% 51.83/6.99      | ~ l1_pre_topc(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k1_tsep_1(X1,X2,X0)
% 51.83/6.99      | sK0 != X1 ),
% 51.83/6.99      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_435,plain,
% 51.83/6.99      ( m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | ~ l1_pre_topc(sK0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(unflattening,[status(thm)],[c_434]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_437,plain,
% 51.83/6.99      ( v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(global_propositional_subsumption,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_435,c_23,c_21]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_438,plain,
% 51.83/6.99      ( m1_pre_topc(X0,X1)
% 51.83/6.99      | ~ m1_pre_topc(X0,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1,sK0)
% 51.83/6.99      | v2_struct_0(X0)
% 51.83/6.99      | v2_struct_0(X1)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK0,X0,X1) ),
% 51.83/6.99      inference(renaming,[status(thm)],[c_437]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_917,plain,
% 51.83/6.99      ( m1_pre_topc(X0_43,X1_43)
% 51.83/6.99      | ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(X1_43,sK0)
% 51.83/6.99      | v2_struct_0(X1_43)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)) != k1_tsep_1(sK0,X0_43,X1_43) ),
% 51.83/6.99      inference(subtyping,[status(esa)],[c_438]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2240,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) != k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),X0_43) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_917]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_5133,plain,
% 51.83/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 51.83/6.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_2240]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_2529,plain,
% 51.83/6.99      ( ~ m1_pre_topc(X0_43,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,X0_43)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(X0_43)
% 51.83/6.99      | v2_struct_0(sK1)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(sK0,sK1,X0_43) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_918]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_3342,plain,
% 51.83/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK2)
% 51.83/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.83/6.99      | v2_struct_0(sK2)
% 51.83/6.99      | v2_struct_0(sK1)
% 51.83/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.83/6.99      inference(instantiation,[status(thm)],[c_2529]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(c_12,negated_conjecture,
% 51.83/6.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 51.83/6.99      inference(cnf_transformation,[],[f56]) ).
% 51.83/6.99  
% 51.83/6.99  cnf(contradiction,plain,
% 51.83/6.99      ( $false ),
% 51.83/6.99      inference(minisat,
% 51.83/6.99                [status(thm)],
% 51.83/6.99                [c_128779,c_115716,c_108788,c_34350,c_19757,c_5133,
% 51.83/6.99                 c_3342,c_1576,c_1514,c_12,c_14,c_15,c_16,c_17,c_18,c_19,
% 51.83/6.99                 c_20]) ).
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.83/6.99  
% 51.83/6.99  ------                               Statistics
% 51.83/6.99  
% 51.83/6.99  ------ General
% 51.83/6.99  
% 51.83/6.99  abstr_ref_over_cycles:                  0
% 51.83/6.99  abstr_ref_under_cycles:                 0
% 51.83/6.99  gc_basic_clause_elim:                   0
% 51.83/6.99  forced_gc_time:                         0
% 51.83/6.99  parsing_time:                           0.008
% 51.83/6.99  unif_index_cands_time:                  0.
% 51.83/6.99  unif_index_add_time:                    0.
% 51.83/6.99  orderings_time:                         0.
% 51.83/6.99  out_proof_time:                         0.032
% 51.83/6.99  total_time:                             6.476
% 51.83/6.99  num_of_symbols:                         49
% 51.83/6.99  num_of_terms:                           167797
% 51.83/6.99  
% 51.83/6.99  ------ Preprocessing
% 51.83/6.99  
% 51.83/6.99  num_of_splits:                          0
% 51.83/6.99  num_of_split_atoms:                     0
% 51.83/6.99  num_of_reused_defs:                     0
% 51.83/6.99  num_eq_ax_congr_red:                    3
% 51.83/6.99  num_of_sem_filtered_clauses:            1
% 51.83/6.99  num_of_subtypes:                        3
% 51.83/6.99  monotx_restored_types:                  0
% 51.83/6.99  sat_num_of_epr_types:                   0
% 51.83/6.99  sat_num_of_non_cyclic_types:            0
% 51.83/6.99  sat_guarded_non_collapsed_types:        1
% 51.83/6.99  num_pure_diseq_elim:                    0
% 51.83/6.99  simp_replaced_by:                       0
% 51.83/6.99  res_preprocessed:                       109
% 51.83/6.99  prep_upred:                             0
% 51.83/6.99  prep_unflattend:                        15
% 51.83/6.99  smt_new_axioms:                         0
% 51.83/6.99  pred_elim_cands:                        3
% 51.83/6.99  pred_elim:                              3
% 51.83/6.99  pred_elim_cl:                           4
% 51.83/6.99  pred_elim_cycles:                       6
% 51.83/6.99  merged_defs:                            0
% 51.83/6.99  merged_defs_ncl:                        0
% 51.83/6.99  bin_hyper_res:                          0
% 51.83/6.99  prep_cycles:                            4
% 51.83/6.99  pred_elim_time:                         0.013
% 51.83/6.99  splitting_time:                         0.
% 51.83/6.99  sem_filter_time:                        0.
% 51.83/6.99  monotx_time:                            0.
% 51.83/6.99  subtype_inf_time:                       0.
% 51.83/6.99  
% 51.83/6.99  ------ Problem properties
% 51.83/6.99  
% 51.83/6.99  clauses:                                20
% 51.83/6.99  conjectures:                            10
% 51.83/6.99  epr:                                    9
% 51.83/6.99  horn:                                   11
% 51.83/6.99  ground:                                 10
% 51.83/6.99  unary:                                  10
% 51.83/6.99  binary:                                 0
% 51.83/6.99  lits:                                   69
% 51.83/6.99  lits_eq:                                7
% 51.83/6.99  fd_pure:                                0
% 51.83/6.99  fd_pseudo:                              0
% 51.83/6.99  fd_cond:                                0
% 51.83/6.99  fd_pseudo_cond:                         1
% 51.83/6.99  ac_symbols:                             0
% 51.83/6.99  
% 51.83/6.99  ------ Propositional Solver
% 51.83/6.99  
% 51.83/6.99  prop_solver_calls:                      65
% 51.83/6.99  prop_fast_solver_calls:                 5945
% 51.83/6.99  smt_solver_calls:                       0
% 51.83/6.99  smt_fast_solver_calls:                  0
% 51.83/6.99  prop_num_of_clauses:                    64445
% 51.83/6.99  prop_preprocess_simplified:             59574
% 51.83/6.99  prop_fo_subsumed:                       1192
% 51.83/6.99  prop_solver_time:                       0.
% 51.83/6.99  smt_solver_time:                        0.
% 51.83/6.99  smt_fast_solver_time:                   0.
% 51.83/6.99  prop_fast_solver_time:                  0.
% 51.83/6.99  prop_unsat_core_time:                   0.006
% 51.83/6.99  
% 51.83/6.99  ------ QBF
% 51.83/6.99  
% 51.83/6.99  qbf_q_res:                              0
% 51.83/6.99  qbf_num_tautologies:                    0
% 51.83/6.99  qbf_prep_cycles:                        0
% 51.83/6.99  
% 51.83/6.99  ------ BMC1
% 51.83/6.99  
% 51.83/6.99  bmc1_current_bound:                     -1
% 51.83/6.99  bmc1_last_solved_bound:                 -1
% 51.83/6.99  bmc1_unsat_core_size:                   -1
% 51.83/6.99  bmc1_unsat_core_parents_size:           -1
% 51.83/6.99  bmc1_merge_next_fun:                    0
% 51.83/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.83/6.99  
% 51.83/6.99  ------ Instantiation
% 51.83/6.99  
% 51.83/6.99  inst_num_of_clauses:                    3795
% 51.83/6.99  inst_num_in_passive:                    1491
% 51.83/6.99  inst_num_in_active:                     4232
% 51.83/6.99  inst_num_in_unprocessed:                897
% 51.83/6.99  inst_num_of_loops:                      4444
% 51.83/6.99  inst_num_of_learning_restarts:          1
% 51.83/6.99  inst_num_moves_active_passive:          204
% 51.83/6.99  inst_lit_activity:                      0
% 51.83/6.99  inst_lit_activity_moves:                2
% 51.83/6.99  inst_num_tautologies:                   0
% 51.83/6.99  inst_num_prop_implied:                  0
% 51.83/6.99  inst_num_existing_simplified:           0
% 51.83/6.99  inst_num_eq_res_simplified:             0
% 51.83/6.99  inst_num_child_elim:                    0
% 51.83/6.99  inst_num_of_dismatching_blockings:      21959
% 51.83/6.99  inst_num_of_non_proper_insts:           16898
% 51.83/6.99  inst_num_of_duplicates:                 0
% 51.83/6.99  inst_inst_num_from_inst_to_res:         0
% 51.83/6.99  inst_dismatching_checking_time:         0.
% 51.83/6.99  
% 51.83/6.99  ------ Resolution
% 51.83/6.99  
% 51.83/6.99  res_num_of_clauses:                     32
% 51.83/6.99  res_num_in_passive:                     32
% 51.83/6.99  res_num_in_active:                      0
% 51.83/6.99  res_num_of_loops:                       113
% 51.83/6.99  res_forward_subset_subsumed:            213
% 51.83/6.99  res_backward_subset_subsumed:           0
% 51.83/6.99  res_forward_subsumed:                   0
% 51.83/6.99  res_backward_subsumed:                  0
% 51.83/6.99  res_forward_subsumption_resolution:     5
% 51.83/6.99  res_backward_subsumption_resolution:    0
% 51.83/6.99  res_clause_to_clause_subsumption:       60748
% 51.83/6.99  res_orphan_elimination:                 0
% 51.83/6.99  res_tautology_del:                      1348
% 51.83/6.99  res_num_eq_res_simplified:              0
% 51.83/6.99  res_num_sel_changes:                    0
% 51.83/6.99  res_moves_from_active_to_pass:          0
% 51.83/6.99  
% 51.83/6.99  ------ Superposition
% 51.83/6.99  
% 51.83/6.99  sup_time_total:                         0.
% 51.83/6.99  sup_time_generating:                    0.
% 51.83/6.99  sup_time_sim_full:                      0.
% 51.83/6.99  sup_time_sim_immed:                     0.
% 51.83/6.99  
% 51.83/6.99  sup_num_of_clauses:                     13981
% 51.83/6.99  sup_num_in_active:                      707
% 51.83/6.99  sup_num_in_passive:                     13274
% 51.83/6.99  sup_num_of_loops:                       888
% 51.83/6.99  sup_fw_superposition:                   6342
% 51.83/6.99  sup_bw_superposition:                   7935
% 51.83/6.99  sup_immediate_simplified:               1233
% 51.83/6.99  sup_given_eliminated:                   2
% 51.83/6.99  comparisons_done:                       0
% 51.83/6.99  comparisons_avoided:                    0
% 51.83/6.99  
% 51.83/6.99  ------ Simplifications
% 51.83/6.99  
% 51.83/6.99  
% 51.83/6.99  sim_fw_subset_subsumed:                 13
% 51.83/6.99  sim_bw_subset_subsumed:                 35
% 51.83/6.99  sim_fw_subsumed:                        30
% 51.83/6.99  sim_bw_subsumed:                        35
% 51.83/6.99  sim_fw_subsumption_res:                 0
% 51.83/6.99  sim_bw_subsumption_res:                 0
% 51.83/6.99  sim_tautology_del:                      4
% 51.83/6.99  sim_eq_tautology_del:                   111
% 51.83/6.99  sim_eq_res_simp:                        3
% 51.83/6.99  sim_fw_demodulated:                     28
% 51.83/6.99  sim_bw_demodulated:                     179
% 51.83/6.99  sim_light_normalised:                   1252
% 51.83/6.99  sim_joinable_taut:                      0
% 51.83/6.99  sim_joinable_simp:                      0
% 51.83/6.99  sim_ac_normalised:                      0
% 51.83/6.99  sim_smt_subsumption:                    0
% 51.83/6.99  
%------------------------------------------------------------------------------
