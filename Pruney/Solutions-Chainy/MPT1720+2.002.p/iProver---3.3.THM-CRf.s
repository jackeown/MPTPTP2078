%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:07 EST 2020

% Result     : Theorem 23.82s
% Output     : CNFRefutation 23.82s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 740 expanded)
%              Number of clauses        :  109 ( 189 expanded)
%              Number of leaves         :   19 ( 254 expanded)
%              Depth                    :   20
%              Number of atoms          :  744 (6710 expanded)
%              Number of equality atoms :  167 ( 239 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f45])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_368,plain,
    ( X0 != X1
    | X2 != X3
    | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_366,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4074,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
    | l1_pre_topc(g1_pre_topc(X2,X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_368,c_366])).

cnf(c_361,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_22216,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
    | l1_pre_topc(g1_pre_topc(X2,X1))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_4074,c_361])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22358,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ l1_pre_topc(g1_pre_topc(X0,X2))
    | l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(resolution,[status(thm)],[c_22216,c_0])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5678,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tsep_1(X1,X0,X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_366])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4226,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tsep_1(X1,X0,X2)) ),
    inference(resolution,[status(thm)],[c_10,c_4])).

cnf(c_12620,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_5678,c_4226])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20320,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_12620,c_17])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1324,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1476,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1478,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_22002,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20320,c_26,c_25,c_22,c_21,c_20,c_1324,c_1478])).

cnf(c_67946,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0)
    | l1_pre_topc(g1_pre_topc(X0,u1_pre_topc(sK3))) ),
    inference(resolution,[status(thm)],[c_22358,c_22002])).

cnf(c_367,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_22365,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),X1))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X2),X1))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_22216,c_367])).

cnf(c_68284,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(sK3)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_67946,c_22365])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5626,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_15,c_2])).

cnf(c_8357,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_5626,c_21])).

cnf(c_1594,plain,
    ( m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3161,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1200,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3162,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_8871,plain,
    ( m1_pre_topc(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8357,c_26,c_25,c_21,c_3161,c_3162])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8902,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_8871,c_14])).

cnf(c_9529,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8902,c_26,c_25,c_21,c_1324,c_1478])).

cnf(c_88250,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(sK3)))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_68284,c_9529])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1205,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1641,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_1215,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1656,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1747,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_10795,plain,
    ( u1_struct_0(sK2) = u1_struct_0(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_362,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3521,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_13953,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_23794,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_807,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_806,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_222,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_12,c_11,c_10])).

cnf(c_223,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_795,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1670,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_795])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1325,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_6584,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1670,c_30,c_31,c_33,c_1325])).

cnf(c_6585,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6584])).

cnf(c_6594,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_6585])).

cnf(c_805,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_801,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1503,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0))
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_795])).

cnf(c_28,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2913,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1503,c_28,c_30,c_31])).

cnf(c_2914,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0))
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2913])).

cnf(c_2922,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_2914])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2941,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2922,c_35])).

cnf(c_6609,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6594,c_2941])).

cnf(c_30908,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6609,c_35])).

cnf(c_814,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_810,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4749,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X3) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(X1,X0,X2)),u1_struct_0(X3)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_810])).

cnf(c_30971,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_30908,c_4749])).

cnf(c_31451,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30971])).

cnf(c_5382,plain,
    ( ~ r1_tarski(X0,k1_tsep_1(sK2,sK1,sK3))
    | ~ r1_tarski(k1_tsep_1(sK2,sK1,sK3),X0)
    | X0 = k1_tsep_1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_33975,plain,
    ( ~ r1_tarski(k1_tsep_1(sK2,sK1,sK3),k1_tsep_1(sK2,sK1,sK3))
    | k1_tsep_1(sK2,sK1,sK3) = k1_tsep_1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_5382])).

cnf(c_33976,plain,
    ( r1_tarski(k1_tsep_1(sK2,sK1,sK3),k1_tsep_1(sK2,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_40047,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_365,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10073,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_23250,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(X1,sK2)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_10073])).

cnf(c_59082,plain,
    ( m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | X0 != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_23250])).

cnf(c_363,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1271,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
    | u1_struct_0(X2) != X0
    | u1_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_3167,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
    | u1_struct_0(X2) != X0
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_10794,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
    | u1_struct_0(X2) != X0
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_3167])).

cnf(c_44163,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != X0
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_10794])).

cnf(c_77067,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_44163])).

cnf(c_10083,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X2)
    | X2 != X1
    | k1_tsep_1(sK2,sK1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_40392,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
    | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X1)
    | X1 != X0
    | k1_tsep_1(sK2,sK1,sK3) != k1_tsep_1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_10083])).

cnf(c_86460,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | X0 != sK2
    | k1_tsep_1(sK2,sK1,sK3) != k1_tsep_1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_40392])).

cnf(c_88285,plain,
    ( X0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_88250,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_1324,c_1478,c_1641,c_1656,c_1747,c_3161,c_3162,c_10795,c_13953,c_23794,c_31451,c_33975,c_33976,c_40047,c_59082,c_77067,c_86460])).

cnf(c_88939,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_88285,c_361])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.82/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.82/3.50  
% 23.82/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.82/3.50  
% 23.82/3.50  ------  iProver source info
% 23.82/3.50  
% 23.82/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.82/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.82/3.50  git: non_committed_changes: false
% 23.82/3.50  git: last_make_outside_of_git: false
% 23.82/3.50  
% 23.82/3.50  ------ 
% 23.82/3.50  ------ Parsing...
% 23.82/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.82/3.50  
% 23.82/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.82/3.50  
% 23.82/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.82/3.50  
% 23.82/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.82/3.50  ------ Proving...
% 23.82/3.50  ------ Problem Properties 
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  clauses                                 26
% 23.82/3.50  conjectures                             12
% 23.82/3.50  EPR                                     15
% 23.82/3.50  Horn                                    20
% 23.82/3.50  unary                                   13
% 23.82/3.50  binary                                  0
% 23.82/3.50  lits                                    86
% 23.82/3.50  lits eq                                 5
% 23.82/3.50  fd_pure                                 0
% 23.82/3.50  fd_pseudo                               0
% 23.82/3.50  fd_cond                                 0
% 23.82/3.50  fd_pseudo_cond                          2
% 23.82/3.50  AC symbols                              0
% 23.82/3.50  
% 23.82/3.50  ------ Input Options Time Limit: Unbounded
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  ------ 
% 23.82/3.50  Current options:
% 23.82/3.50  ------ 
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  ------ Proving...
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  % SZS status Theorem for theBenchmark.p
% 23.82/3.50  
% 23.82/3.50   Resolution empty clause
% 23.82/3.50  
% 23.82/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.82/3.50  
% 23.82/3.50  fof(f1,axiom,(
% 23.82/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f27,plain,(
% 23.82/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.82/3.50    inference(nnf_transformation,[],[f1])).
% 23.82/3.50  
% 23.82/3.50  fof(f28,plain,(
% 23.82/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.82/3.50    inference(flattening,[],[f27])).
% 23.82/3.50  
% 23.82/3.50  fof(f39,plain,(
% 23.82/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f28])).
% 23.82/3.50  
% 23.82/3.50  fof(f8,axiom,(
% 23.82/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f21,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f8])).
% 23.82/3.50  
% 23.82/3.50  fof(f22,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.82/3.50    inference(flattening,[],[f21])).
% 23.82/3.50  
% 23.82/3.50  fof(f50,plain,(
% 23.82/3.50    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f22])).
% 23.82/3.50  
% 23.82/3.50  fof(f7,axiom,(
% 23.82/3.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f19,plain,(
% 23.82/3.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f7])).
% 23.82/3.50  
% 23.82/3.50  fof(f20,plain,(
% 23.82/3.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.82/3.50    inference(flattening,[],[f19])).
% 23.82/3.50  
% 23.82/3.50  fof(f49,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f20])).
% 23.82/3.50  
% 23.82/3.50  fof(f3,axiom,(
% 23.82/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f14,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.82/3.50    inference(ennf_transformation,[],[f3])).
% 23.82/3.50  
% 23.82/3.50  fof(f41,plain,(
% 23.82/3.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f14])).
% 23.82/3.50  
% 23.82/3.50  fof(f10,conjecture,(
% 23.82/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f11,negated_conjecture,(
% 23.82/3.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 23.82/3.50    inference(negated_conjecture,[],[f10])).
% 23.82/3.50  
% 23.82/3.50  fof(f25,plain,(
% 23.82/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f11])).
% 23.82/3.50  
% 23.82/3.50  fof(f26,plain,(
% 23.82/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.82/3.50    inference(flattening,[],[f25])).
% 23.82/3.50  
% 23.82/3.50  fof(f35,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 23.82/3.50    introduced(choice_axiom,[])).
% 23.82/3.50  
% 23.82/3.50  fof(f34,plain,(
% 23.82/3.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 23.82/3.50    introduced(choice_axiom,[])).
% 23.82/3.50  
% 23.82/3.50  fof(f33,plain,(
% 23.82/3.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 23.82/3.50    introduced(choice_axiom,[])).
% 23.82/3.50  
% 23.82/3.50  fof(f32,plain,(
% 23.82/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 23.82/3.50    introduced(choice_axiom,[])).
% 23.82/3.50  
% 23.82/3.50  fof(f36,plain,(
% 23.82/3.50    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 23.82/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).
% 23.82/3.50  
% 23.82/3.50  fof(f63,plain,(
% 23.82/3.50    m1_pre_topc(sK3,sK2)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f54,plain,(
% 23.82/3.50    v2_pre_topc(sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f55,plain,(
% 23.82/3.50    l1_pre_topc(sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f58,plain,(
% 23.82/3.50    ~v2_struct_0(sK2)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f59,plain,(
% 23.82/3.50    m1_pre_topc(sK2,sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f60,plain,(
% 23.82/3.50    ~v2_struct_0(sK3)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f2,axiom,(
% 23.82/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f12,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f2])).
% 23.82/3.50  
% 23.82/3.50  fof(f13,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.82/3.50    inference(flattening,[],[f12])).
% 23.82/3.50  
% 23.82/3.50  fof(f40,plain,(
% 23.82/3.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f13])).
% 23.82/3.50  
% 23.82/3.50  fof(f9,axiom,(
% 23.82/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f23,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f9])).
% 23.82/3.50  
% 23.82/3.50  fof(f24,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.82/3.50    inference(flattening,[],[f23])).
% 23.82/3.50  
% 23.82/3.50  fof(f31,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.82/3.50    inference(nnf_transformation,[],[f24])).
% 23.82/3.50  
% 23.82/3.50  fof(f51,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f31])).
% 23.82/3.50  
% 23.82/3.50  fof(f37,plain,(
% 23.82/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.82/3.50    inference(cnf_transformation,[],[f28])).
% 23.82/3.50  
% 23.82/3.50  fof(f66,plain,(
% 23.82/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.82/3.50    inference(equality_resolution,[],[f37])).
% 23.82/3.50  
% 23.82/3.50  fof(f52,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f31])).
% 23.82/3.50  
% 23.82/3.50  fof(f53,plain,(
% 23.82/3.50    ~v2_struct_0(sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f56,plain,(
% 23.82/3.50    ~v2_struct_0(sK1)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f57,plain,(
% 23.82/3.50    m1_pre_topc(sK1,sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f61,plain,(
% 23.82/3.50    m1_pre_topc(sK3,sK0)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f62,plain,(
% 23.82/3.50    m1_pre_topc(sK1,sK2)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f64,plain,(
% 23.82/3.50    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 23.82/3.50    inference(cnf_transformation,[],[f36])).
% 23.82/3.50  
% 23.82/3.50  fof(f6,axiom,(
% 23.82/3.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 23.82/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.82/3.50  
% 23.82/3.50  fof(f17,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.82/3.50    inference(ennf_transformation,[],[f6])).
% 23.82/3.50  
% 23.82/3.50  fof(f18,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.82/3.50    inference(flattening,[],[f17])).
% 23.82/3.50  
% 23.82/3.50  fof(f30,plain,(
% 23.82/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.82/3.50    inference(nnf_transformation,[],[f18])).
% 23.82/3.50  
% 23.82/3.50  fof(f45,plain,(
% 23.82/3.50    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f30])).
% 23.82/3.50  
% 23.82/3.50  fof(f67,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(equality_resolution,[],[f45])).
% 23.82/3.50  
% 23.82/3.50  fof(f47,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f20])).
% 23.82/3.50  
% 23.82/3.50  fof(f48,plain,(
% 23.82/3.50    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.82/3.50    inference(cnf_transformation,[],[f20])).
% 23.82/3.50  
% 23.82/3.50  cnf(c_368,plain,
% 23.82/3.50      ( X0 != X1 | X2 != X3 | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
% 23.82/3.50      theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_366,plain,
% 23.82/3.50      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 23.82/3.50      theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_4074,plain,
% 23.82/3.50      ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(X2,X3))
% 23.82/3.50      | X2 != X0
% 23.82/3.50      | X3 != X1 ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_368,c_366]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_361,plain,( X0 = X0 ),theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_22216,plain,
% 23.82/3.50      ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(X2,X1))
% 23.82/3.50      | X2 != X0 ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_4074,c_361]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_0,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.82/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_22358,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,X1)
% 23.82/3.50      | ~ r1_tarski(X1,X0)
% 23.82/3.50      | ~ l1_pre_topc(g1_pre_topc(X0,X2))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(X1,X2)) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_22216,c_0]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_13,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ v2_pre_topc(X1)
% 23.82/3.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_5678,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ l1_pre_topc(k1_tsep_1(X1,X0,X0))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 23.82/3.50      | ~ v2_pre_topc(X1) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_13,c_366]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_10,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | ~ l1_pre_topc(X1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_4,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_4226,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | l1_pre_topc(k1_tsep_1(X1,X0,X2)) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_10,c_4]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_12620,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 23.82/3.50      | ~ v2_pre_topc(X1) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_5678,c_4226]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_17,negated_conjecture,
% 23.82/3.50      ( m1_pre_topc(sK3,sK2) ),
% 23.82/3.50      inference(cnf_transformation,[],[f63]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_20320,plain,
% 23.82/3.50      ( v2_struct_0(sK2)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.82/3.50      | ~ l1_pre_topc(sK2)
% 23.82/3.50      | ~ v2_pre_topc(sK2) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_12620,c_17]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_26,negated_conjecture,
% 23.82/3.50      ( v2_pre_topc(sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_25,negated_conjecture,
% 23.82/3.50      ( l1_pre_topc(sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_22,negated_conjecture,
% 23.82/3.50      ( ~ v2_struct_0(sK2) ),
% 23.82/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_21,negated_conjecture,
% 23.82/3.50      ( m1_pre_topc(sK2,sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f59]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_20,negated_conjecture,
% 23.82/3.50      ( ~ v2_struct_0(sK3) ),
% 23.82/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1324,plain,
% 23.82/3.50      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_4,c_21]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_3,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ v2_pre_topc(X1)
% 23.82/3.50      | v2_pre_topc(X0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1476,plain,
% 23.82/3.50      ( ~ m1_pre_topc(sK2,X0)
% 23.82/3.50      | ~ l1_pre_topc(X0)
% 23.82/3.50      | ~ v2_pre_topc(X0)
% 23.82/3.50      | v2_pre_topc(sK2) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1478,plain,
% 23.82/3.50      ( ~ m1_pre_topc(sK2,sK0)
% 23.82/3.50      | ~ l1_pre_topc(sK0)
% 23.82/3.50      | v2_pre_topc(sK2)
% 23.82/3.50      | ~ v2_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1476]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_22002,plain,
% 23.82/3.50      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_20320,c_26,c_25,c_22,c_21,c_20,c_1324,c_1478]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_67946,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(sK3),X0)
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(X0,u1_pre_topc(sK3))) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_22358,c_22002]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_367,plain,
% 23.82/3.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.82/3.50      theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_22365,plain,
% 23.82/3.50      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),X1))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X2),X1))
% 23.82/3.50      | X2 != X0 ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_22216,c_367]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_68284,plain,
% 23.82/3.50      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(sK3)))
% 23.82/3.50      | X1 != X0 ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_67946,c_22365]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_15,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | m1_pre_topc(X0,X2)
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ v2_pre_topc(X1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f66]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_5626,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | m1_pre_topc(X0,X0)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ v2_pre_topc(X1) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_15,c_2]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_8357,plain,
% 23.82/3.50      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_5626,c_21]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1594,plain,
% 23.82/3.50      ( m1_pre_topc(X0,sK2)
% 23.82/3.50      | ~ m1_pre_topc(X0,sK0)
% 23.82/3.50      | ~ m1_pre_topc(sK2,sK0)
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 23.82/3.50      | ~ l1_pre_topc(sK0)
% 23.82/3.50      | ~ v2_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_15]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_3161,plain,
% 23.82/3.50      ( m1_pre_topc(sK2,sK2)
% 23.82/3.50      | ~ m1_pre_topc(sK2,sK0)
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
% 23.82/3.50      | ~ l1_pre_topc(sK0)
% 23.82/3.50      | ~ v2_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1594]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1200,plain,
% 23.82/3.50      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_3162,plain,
% 23.82/3.50      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1200]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_8871,plain,
% 23.82/3.50      ( m1_pre_topc(sK2,sK2) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_8357,c_26,c_25,c_21,c_3161,c_3162]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_14,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | ~ m1_pre_topc(X0,X2)
% 23.82/3.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | ~ v2_pre_topc(X1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f52]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_8902,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.82/3.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 23.82/3.50      | ~ l1_pre_topc(sK2)
% 23.82/3.50      | ~ v2_pre_topc(sK2) ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_8871,c_14]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_9529,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_8902,c_26,c_25,c_21,c_1324,c_1478]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_88250,plain,
% 23.82/3.50      ( ~ m1_pre_topc(sK3,sK2)
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 23.82/3.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(sK3)))
% 23.82/3.50      | X0 != sK2 ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_68284,c_9529]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_27,negated_conjecture,
% 23.82/3.50      ( ~ v2_struct_0(sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_24,negated_conjecture,
% 23.82/3.50      ( ~ v2_struct_0(sK1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_23,negated_conjecture,
% 23.82/3.50      ( m1_pre_topc(sK1,sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_19,negated_conjecture,
% 23.82/3.50      ( m1_pre_topc(sK3,sK0) ),
% 23.82/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_18,negated_conjecture,
% 23.82/3.50      ( m1_pre_topc(sK1,sK2) ),
% 23.82/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_16,negated_conjecture,
% 23.82/3.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 23.82/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1205,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(sK2,X0,sK3),sK2)
% 23.82/3.50      | ~ m1_pre_topc(sK3,sK2)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(sK2)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | ~ l1_pre_topc(sK2) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1641,plain,
% 23.82/3.50      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 23.82/3.50      | ~ m1_pre_topc(sK3,sK2)
% 23.82/3.50      | ~ m1_pre_topc(sK1,sK2)
% 23.82/3.50      | v2_struct_0(sK2)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | v2_struct_0(sK1)
% 23.82/3.50      | ~ l1_pre_topc(sK2) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1205]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1215,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK0)
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(sK0,X0,sK3),sK0)
% 23.82/3.50      | ~ m1_pre_topc(sK3,sK0)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | v2_struct_0(sK0)
% 23.82/3.50      | ~ l1_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1656,plain,
% 23.82/3.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 23.82/3.50      | ~ m1_pre_topc(sK3,sK0)
% 23.82/3.50      | ~ m1_pre_topc(sK1,sK0)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | v2_struct_0(sK1)
% 23.82/3.50      | v2_struct_0(sK0)
% 23.82/3.50      | ~ l1_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1215]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1747,plain,
% 23.82/3.50      ( sK2 = sK2 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_361]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_10795,plain,
% 23.82/3.50      ( u1_struct_0(sK2) = u1_struct_0(X0) | sK2 != X0 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_367]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_362,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_3521,plain,
% 23.82/3.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_362]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_13953,plain,
% 23.82/3.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_3521]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_23794,plain,
% 23.82/3.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 23.82/3.50      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 23.82/3.50      | ~ m1_pre_topc(sK2,sK0)
% 23.82/3.50      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 23.82/3.50      | ~ l1_pre_topc(sK0)
% 23.82/3.50      | ~ v2_pre_topc(sK0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1594]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_807,plain,
% 23.82/3.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_806,plain,
% 23.82/3.50      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_9,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 23.82/3.50      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 23.82/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_12,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 23.82/3.50      | ~ l1_pre_topc(X1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_11,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 23.82/3.50      | ~ l1_pre_topc(X1) ),
% 23.82/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_222,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_9,c_12,c_11,c_10]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_223,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | ~ m1_pre_topc(X2,X1)
% 23.82/3.50      | v2_struct_0(X0)
% 23.82/3.50      | v2_struct_0(X1)
% 23.82/3.50      | v2_struct_0(X2)
% 23.82/3.50      | ~ l1_pre_topc(X1)
% 23.82/3.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 23.82/3.50      inference(renaming,[status(thm)],[c_222]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_795,plain,
% 23.82/3.50      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 23.82/3.50      | m1_pre_topc(X1,X0) != iProver_top
% 23.82/3.50      | m1_pre_topc(X2,X0) != iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top
% 23.82/3.50      | v2_struct_0(X1) = iProver_top
% 23.82/3.50      | v2_struct_0(X2) = iProver_top
% 23.82/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1670,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0))
% 23.82/3.50      | m1_pre_topc(X0,sK2) != iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top
% 23.82/3.50      | v2_struct_0(sK2) = iProver_top
% 23.82/3.50      | v2_struct_0(sK1) = iProver_top
% 23.82/3.50      | l1_pre_topc(sK2) != iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_806,c_795]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_30,plain,
% 23.82/3.50      ( l1_pre_topc(sK0) = iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_31,plain,
% 23.82/3.50      ( v2_struct_0(sK1) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_33,plain,
% 23.82/3.50      ( v2_struct_0(sK2) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1325,plain,
% 23.82/3.50      ( l1_pre_topc(sK2) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_6584,plain,
% 23.82/3.50      ( v2_struct_0(X0) = iProver_top
% 23.82/3.50      | m1_pre_topc(X0,sK2) != iProver_top
% 23.82/3.50      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0)) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_1670,c_30,c_31,c_33,c_1325]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_6585,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0))
% 23.82/3.50      | m1_pre_topc(X0,sK2) != iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top ),
% 23.82/3.50      inference(renaming,[status(thm)],[c_6584]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_6594,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 23.82/3.50      | v2_struct_0(sK3) = iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_807,c_6585]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_805,plain,
% 23.82/3.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_801,plain,
% 23.82/3.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1503,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0))
% 23.82/3.50      | m1_pre_topc(X0,sK0) != iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top
% 23.82/3.50      | v2_struct_0(sK1) = iProver_top
% 23.82/3.50      | v2_struct_0(sK0) = iProver_top
% 23.82/3.50      | l1_pre_topc(sK0) != iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_801,c_795]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_28,plain,
% 23.82/3.50      ( v2_struct_0(sK0) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_2913,plain,
% 23.82/3.50      ( v2_struct_0(X0) = iProver_top
% 23.82/3.50      | m1_pre_topc(X0,sK0) != iProver_top
% 23.82/3.50      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0)) ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_1503,c_28,c_30,c_31]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_2914,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0))
% 23.82/3.50      | m1_pre_topc(X0,sK0) != iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top ),
% 23.82/3.50      inference(renaming,[status(thm)],[c_2913]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_2922,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 23.82/3.50      | v2_struct_0(sK3) = iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_805,c_2914]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_35,plain,
% 23.82/3.50      ( v2_struct_0(sK3) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_2941,plain,
% 23.82/3.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 23.82/3.50      inference(global_propositional_subsumption,[status(thm)],[c_2922,c_35]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_6609,plain,
% 23.82/3.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 23.82/3.50      | v2_struct_0(sK3) = iProver_top ),
% 23.82/3.50      inference(light_normalisation,[status(thm)],[c_6594,c_2941]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_30908,plain,
% 23.82/3.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 23.82/3.50      inference(global_propositional_subsumption,[status(thm)],[c_6609,c_35]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_814,plain,
% 23.82/3.50      ( m1_pre_topc(X0,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(X2,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
% 23.82/3.50      | v2_struct_0(X1) = iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top
% 23.82/3.50      | v2_struct_0(X2) = iProver_top
% 23.82/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_810,plain,
% 23.82/3.50      ( m1_pre_topc(X0,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(X2,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(X0,X2) != iProver_top
% 23.82/3.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 23.82/3.50      | l1_pre_topc(X1) != iProver_top
% 23.82/3.50      | v2_pre_topc(X1) != iProver_top ),
% 23.82/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_4749,plain,
% 23.82/3.50      ( m1_pre_topc(X0,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(X2,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(X3,X1) != iProver_top
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X3) != iProver_top
% 23.82/3.50      | r1_tarski(u1_struct_0(k1_tsep_1(X1,X0,X2)),u1_struct_0(X3)) = iProver_top
% 23.82/3.50      | v2_struct_0(X1) = iProver_top
% 23.82/3.50      | v2_struct_0(X0) = iProver_top
% 23.82/3.50      | v2_struct_0(X2) = iProver_top
% 23.82/3.50      | l1_pre_topc(X1) != iProver_top
% 23.82/3.50      | v2_pre_topc(X1) != iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_814,c_810]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_30971,plain,
% 23.82/3.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0) != iProver_top
% 23.82/3.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 23.82/3.50      | m1_pre_topc(sK1,sK2) != iProver_top
% 23.82/3.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top
% 23.82/3.50      | v2_struct_0(sK2) = iProver_top
% 23.82/3.50      | v2_struct_0(sK3) = iProver_top
% 23.82/3.50      | v2_struct_0(sK1) = iProver_top
% 23.82/3.50      | l1_pre_topc(sK2) != iProver_top
% 23.82/3.50      | v2_pre_topc(sK2) != iProver_top ),
% 23.82/3.50      inference(superposition,[status(thm)],[c_30908,c_4749]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_31451,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.82/3.50      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
% 23.82/3.50      | ~ m1_pre_topc(sK3,sK2)
% 23.82/3.50      | ~ m1_pre_topc(sK1,sK2)
% 23.82/3.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0))
% 23.82/3.50      | v2_struct_0(sK2)
% 23.82/3.50      | v2_struct_0(sK3)
% 23.82/3.50      | v2_struct_0(sK1)
% 23.82/3.50      | ~ l1_pre_topc(sK2)
% 23.82/3.50      | ~ v2_pre_topc(sK2) ),
% 23.82/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_30971]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_5382,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,k1_tsep_1(sK2,sK1,sK3))
% 23.82/3.50      | ~ r1_tarski(k1_tsep_1(sK2,sK1,sK3),X0)
% 23.82/3.50      | X0 = k1_tsep_1(sK2,sK1,sK3) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_33975,plain,
% 23.82/3.50      ( ~ r1_tarski(k1_tsep_1(sK2,sK1,sK3),k1_tsep_1(sK2,sK1,sK3))
% 23.82/3.50      | k1_tsep_1(sK2,sK1,sK3) = k1_tsep_1(sK2,sK1,sK3) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_5382]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_33976,plain,
% 23.82/3.50      ( r1_tarski(k1_tsep_1(sK2,sK1,sK3),k1_tsep_1(sK2,sK1,sK3)) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_40047,plain,
% 23.82/3.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_361]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_365,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.82/3.50      theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_10073,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,sK2) | X2 != X0 | sK2 != X1 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_365]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_23250,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,sK2) | m1_pre_topc(X1,sK2) | X1 != X0 | sK2 != sK2 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_10073]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_59082,plain,
% 23.82/3.50      ( m1_pre_topc(X0,sK2) | ~ m1_pre_topc(sK2,sK2) | X0 != sK2 | sK2 != sK2 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_23250]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_363,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.82/3.50      theory(equality) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_1271,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,X1)
% 23.82/3.50      | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
% 23.82/3.50      | u1_struct_0(X2) != X0
% 23.82/3.50      | u1_struct_0(X3) != X1 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_363]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_3167,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,X1)
% 23.82/3.50      | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
% 23.82/3.50      | u1_struct_0(X2) != X0
% 23.82/3.50      | u1_struct_0(sK2) != X1 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_1271]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_10794,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 23.82/3.50      | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
% 23.82/3.50      | u1_struct_0(X2) != X0
% 23.82/3.50      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_3167]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_44163,plain,
% 23.82/3.50      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 23.82/3.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 23.82/3.50      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != X0
% 23.82/3.50      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_10794]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_77067,plain,
% 23.82/3.50      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0))
% 23.82/3.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 23.82/3.50      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 23.82/3.50      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_44163]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_10083,plain,
% 23.82/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X2)
% 23.82/3.50      | X2 != X1
% 23.82/3.50      | k1_tsep_1(sK2,sK1,sK3) != X0 ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_365]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_40392,plain,
% 23.82/3.50      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
% 23.82/3.50      | m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X1)
% 23.82/3.50      | X1 != X0
% 23.82/3.50      | k1_tsep_1(sK2,sK1,sK3) != k1_tsep_1(sK2,sK1,sK3) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_10083]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_86460,plain,
% 23.82/3.50      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0)
% 23.82/3.50      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 23.82/3.50      | X0 != sK2
% 23.82/3.50      | k1_tsep_1(sK2,sK1,sK3) != k1_tsep_1(sK2,sK1,sK3) ),
% 23.82/3.50      inference(instantiation,[status(thm)],[c_40392]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_88285,plain,
% 23.82/3.50      ( X0 != sK2 ),
% 23.82/3.50      inference(global_propositional_subsumption,
% 23.82/3.50                [status(thm)],
% 23.82/3.50                [c_88250,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,
% 23.82/3.50                 c_17,c_16,c_1324,c_1478,c_1641,c_1656,c_1747,c_3161,c_3162,
% 23.82/3.50                 c_10795,c_13953,c_23794,c_31451,c_33975,c_33976,c_40047,
% 23.82/3.50                 c_59082,c_77067,c_86460]) ).
% 23.82/3.50  
% 23.82/3.50  cnf(c_88939,plain,
% 23.82/3.50      ( $false ),
% 23.82/3.50      inference(resolution,[status(thm)],[c_88285,c_361]) ).
% 23.82/3.50  
% 23.82/3.50  
% 23.82/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.82/3.50  
% 23.82/3.50  ------                               Statistics
% 23.82/3.50  
% 23.82/3.50  ------ Selected
% 23.82/3.50  
% 23.82/3.50  total_time:                             2.704
% 23.82/3.50  
%------------------------------------------------------------------------------
