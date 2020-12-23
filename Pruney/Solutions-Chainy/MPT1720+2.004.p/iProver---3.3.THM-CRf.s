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

% Result     : Theorem 31.42s
% Output     : CNFRefutation 31.42s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 461 expanded)
%              Number of clauses        :   84 ( 118 expanded)
%              Number of leaves         :   14 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          :  688 (4413 expanded)
%              Number of equality atoms :  107 ( 134 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f25,plain,(
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

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
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
    inference(equality_resolution,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
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

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_86814,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | X0_44 != u1_struct_0(X0_43)
    | X1_44 != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_87051,plain,
    ( r1_tarski(X0_44,u1_struct_0(X0_43))
    | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X0_43))
    | X0_44 != u1_struct_0(X1_43)
    | u1_struct_0(X0_43) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_86814])).

cnf(c_87248,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X1_43))
    | u1_struct_0(X1_43) != u1_struct_0(X1_43)
    | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_87051])).

cnf(c_90032,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(X1_43,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(X1_43,sK1,sK3)) != u1_struct_0(X0_43)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_87248])).

cnf(c_96652,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_90032])).

cnf(c_96654,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_96652])).

cnf(c_228,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_87052,plain,
    ( u1_struct_0(X0_43) = u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_88280,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_87052])).

cnf(c_11,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_215,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12649,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_65366,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12649])).

cnf(c_10,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_216,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1552,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_6003,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_207,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_664,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_211,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_660,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_181,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_6,c_5,c_4])).

cnf(c_182,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_202,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_669,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_3397,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_669])).

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

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5132,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_24,c_26,c_31])).

cnf(c_5133,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5132])).

cnf(c_5143,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_5133])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_212,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_659,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_213,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_658,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_3395,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_669])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_209,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1192,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_224,c_209])).

cnf(c_1193,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_4537,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3395,c_26,c_29,c_31,c_1193])).

cnf(c_4538,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4537])).

cnf(c_4547,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_4538])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4717,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4547,c_27])).

cnf(c_5163,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5143,c_4717])).

cnf(c_222,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1061,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1328,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1051,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_43,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1313,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_662,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_225,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_646,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1238,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_646])).

cnf(c_1250,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1238])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_219,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(X0_43,X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43)) != k1_tsep_1(X1_43,X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1218,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_217,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1020,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96654,c_88280,c_65366,c_6003,c_5163,c_1328,c_1313,c_1250,c_1218,c_1192,c_1020,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_27,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 31.42/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.42/4.50  
% 31.42/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.42/4.50  
% 31.42/4.50  ------  iProver source info
% 31.42/4.50  
% 31.42/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.42/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.42/4.50  git: non_committed_changes: false
% 31.42/4.50  git: last_make_outside_of_git: false
% 31.42/4.50  
% 31.42/4.50  ------ 
% 31.42/4.50  
% 31.42/4.50  ------ Input Options
% 31.42/4.50  
% 31.42/4.50  --out_options                           all
% 31.42/4.50  --tptp_safe_out                         true
% 31.42/4.50  --problem_path                          ""
% 31.42/4.50  --include_path                          ""
% 31.42/4.50  --clausifier                            res/vclausify_rel
% 31.42/4.50  --clausifier_options                    --mode clausify
% 31.42/4.50  --stdin                                 false
% 31.42/4.50  --stats_out                             sel
% 31.42/4.50  
% 31.42/4.50  ------ General Options
% 31.42/4.50  
% 31.42/4.50  --fof                                   false
% 31.42/4.50  --time_out_real                         604.99
% 31.42/4.50  --time_out_virtual                      -1.
% 31.42/4.50  --symbol_type_check                     false
% 31.42/4.50  --clausify_out                          false
% 31.42/4.50  --sig_cnt_out                           false
% 31.42/4.50  --trig_cnt_out                          false
% 31.42/4.50  --trig_cnt_out_tolerance                1.
% 31.42/4.50  --trig_cnt_out_sk_spl                   false
% 31.42/4.50  --abstr_cl_out                          false
% 31.42/4.50  
% 31.42/4.50  ------ Global Options
% 31.42/4.50  
% 31.42/4.50  --schedule                              none
% 31.42/4.50  --add_important_lit                     false
% 31.42/4.50  --prop_solver_per_cl                    1000
% 31.42/4.50  --min_unsat_core                        false
% 31.42/4.50  --soft_assumptions                      false
% 31.42/4.50  --soft_lemma_size                       3
% 31.42/4.50  --prop_impl_unit_size                   0
% 31.42/4.50  --prop_impl_unit                        []
% 31.42/4.50  --share_sel_clauses                     true
% 31.42/4.50  --reset_solvers                         false
% 31.42/4.50  --bc_imp_inh                            [conj_cone]
% 31.42/4.50  --conj_cone_tolerance                   3.
% 31.42/4.50  --extra_neg_conj                        none
% 31.42/4.50  --large_theory_mode                     true
% 31.42/4.50  --prolific_symb_bound                   200
% 31.42/4.50  --lt_threshold                          2000
% 31.42/4.50  --clause_weak_htbl                      true
% 31.42/4.50  --gc_record_bc_elim                     false
% 31.42/4.50  
% 31.42/4.50  ------ Preprocessing Options
% 31.42/4.50  
% 31.42/4.50  --preprocessing_flag                    true
% 31.42/4.50  --time_out_prep_mult                    0.1
% 31.42/4.50  --splitting_mode                        input
% 31.42/4.50  --splitting_grd                         true
% 31.42/4.50  --splitting_cvd                         false
% 31.42/4.50  --splitting_cvd_svl                     false
% 31.42/4.50  --splitting_nvd                         32
% 31.42/4.50  --sub_typing                            true
% 31.42/4.50  --prep_gs_sim                           false
% 31.42/4.50  --prep_unflatten                        true
% 31.42/4.50  --prep_res_sim                          true
% 31.42/4.50  --prep_upred                            true
% 31.42/4.50  --prep_sem_filter                       exhaustive
% 31.42/4.50  --prep_sem_filter_out                   false
% 31.42/4.50  --pred_elim                             false
% 31.42/4.50  --res_sim_input                         true
% 31.42/4.50  --eq_ax_congr_red                       true
% 31.42/4.50  --pure_diseq_elim                       true
% 31.42/4.50  --brand_transform                       false
% 31.42/4.50  --non_eq_to_eq                          false
% 31.42/4.50  --prep_def_merge                        true
% 31.42/4.50  --prep_def_merge_prop_impl              false
% 31.42/4.50  --prep_def_merge_mbd                    true
% 31.42/4.50  --prep_def_merge_tr_red                 false
% 31.42/4.50  --prep_def_merge_tr_cl                  false
% 31.42/4.50  --smt_preprocessing                     true
% 31.42/4.50  --smt_ac_axioms                         fast
% 31.42/4.50  --preprocessed_out                      false
% 31.42/4.50  --preprocessed_stats                    false
% 31.42/4.50  
% 31.42/4.50  ------ Abstraction refinement Options
% 31.42/4.50  
% 31.42/4.50  --abstr_ref                             []
% 31.42/4.50  --abstr_ref_prep                        false
% 31.42/4.50  --abstr_ref_until_sat                   false
% 31.42/4.50  --abstr_ref_sig_restrict                funpre
% 31.42/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.42/4.50  --abstr_ref_under                       []
% 31.42/4.50  
% 31.42/4.50  ------ SAT Options
% 31.42/4.50  
% 31.42/4.50  --sat_mode                              false
% 31.42/4.50  --sat_fm_restart_options                ""
% 31.42/4.50  --sat_gr_def                            false
% 31.42/4.50  --sat_epr_types                         true
% 31.42/4.50  --sat_non_cyclic_types                  false
% 31.42/4.50  --sat_finite_models                     false
% 31.42/4.50  --sat_fm_lemmas                         false
% 31.42/4.50  --sat_fm_prep                           false
% 31.42/4.50  --sat_fm_uc_incr                        true
% 31.42/4.50  --sat_out_model                         small
% 31.42/4.50  --sat_out_clauses                       false
% 31.42/4.50  
% 31.42/4.50  ------ QBF Options
% 31.42/4.50  
% 31.42/4.50  --qbf_mode                              false
% 31.42/4.50  --qbf_elim_univ                         false
% 31.42/4.50  --qbf_dom_inst                          none
% 31.42/4.50  --qbf_dom_pre_inst                      false
% 31.42/4.50  --qbf_sk_in                             false
% 31.42/4.50  --qbf_pred_elim                         true
% 31.42/4.50  --qbf_split                             512
% 31.42/4.50  
% 31.42/4.50  ------ BMC1 Options
% 31.42/4.50  
% 31.42/4.50  --bmc1_incremental                      false
% 31.42/4.50  --bmc1_axioms                           reachable_all
% 31.42/4.50  --bmc1_min_bound                        0
% 31.42/4.50  --bmc1_max_bound                        -1
% 31.42/4.50  --bmc1_max_bound_default                -1
% 31.42/4.50  --bmc1_symbol_reachability              true
% 31.42/4.50  --bmc1_property_lemmas                  false
% 31.42/4.50  --bmc1_k_induction                      false
% 31.42/4.50  --bmc1_non_equiv_states                 false
% 31.42/4.50  --bmc1_deadlock                         false
% 31.42/4.50  --bmc1_ucm                              false
% 31.42/4.50  --bmc1_add_unsat_core                   none
% 31.42/4.50  --bmc1_unsat_core_children              false
% 31.42/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.42/4.50  --bmc1_out_stat                         full
% 31.42/4.50  --bmc1_ground_init                      false
% 31.42/4.50  --bmc1_pre_inst_next_state              false
% 31.42/4.50  --bmc1_pre_inst_state                   false
% 31.42/4.50  --bmc1_pre_inst_reach_state             false
% 31.42/4.50  --bmc1_out_unsat_core                   false
% 31.42/4.50  --bmc1_aig_witness_out                  false
% 31.42/4.50  --bmc1_verbose                          false
% 31.42/4.50  --bmc1_dump_clauses_tptp                false
% 31.42/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.42/4.50  --bmc1_dump_file                        -
% 31.42/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.42/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.42/4.50  --bmc1_ucm_extend_mode                  1
% 31.42/4.50  --bmc1_ucm_init_mode                    2
% 31.42/4.50  --bmc1_ucm_cone_mode                    none
% 31.42/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.42/4.50  --bmc1_ucm_relax_model                  4
% 31.42/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.42/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.42/4.50  --bmc1_ucm_layered_model                none
% 31.42/4.50  --bmc1_ucm_max_lemma_size               10
% 31.42/4.50  
% 31.42/4.50  ------ AIG Options
% 31.42/4.50  
% 31.42/4.50  --aig_mode                              false
% 31.42/4.50  
% 31.42/4.50  ------ Instantiation Options
% 31.42/4.50  
% 31.42/4.50  --instantiation_flag                    true
% 31.42/4.50  --inst_sos_flag                         false
% 31.42/4.50  --inst_sos_phase                        true
% 31.42/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.42/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.42/4.50  --inst_lit_sel_side                     num_symb
% 31.42/4.50  --inst_solver_per_active                1400
% 31.42/4.50  --inst_solver_calls_frac                1.
% 31.42/4.50  --inst_passive_queue_type               priority_queues
% 31.42/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.42/4.50  --inst_passive_queues_freq              [25;2]
% 31.42/4.50  --inst_dismatching                      true
% 31.42/4.50  --inst_eager_unprocessed_to_passive     true
% 31.42/4.50  --inst_prop_sim_given                   true
% 31.42/4.50  --inst_prop_sim_new                     false
% 31.42/4.50  --inst_subs_new                         false
% 31.42/4.50  --inst_eq_res_simp                      false
% 31.42/4.50  --inst_subs_given                       false
% 31.42/4.50  --inst_orphan_elimination               true
% 31.42/4.50  --inst_learning_loop_flag               true
% 31.42/4.50  --inst_learning_start                   3000
% 31.42/4.50  --inst_learning_factor                  2
% 31.42/4.50  --inst_start_prop_sim_after_learn       3
% 31.42/4.50  --inst_sel_renew                        solver
% 31.42/4.50  --inst_lit_activity_flag                true
% 31.42/4.50  --inst_restr_to_given                   false
% 31.42/4.50  --inst_activity_threshold               500
% 31.42/4.50  --inst_out_proof                        true
% 31.42/4.50  
% 31.42/4.50  ------ Resolution Options
% 31.42/4.50  
% 31.42/4.50  --resolution_flag                       true
% 31.42/4.50  --res_lit_sel                           adaptive
% 31.42/4.50  --res_lit_sel_side                      none
% 31.42/4.50  --res_ordering                          kbo
% 31.42/4.50  --res_to_prop_solver                    active
% 31.42/4.50  --res_prop_simpl_new                    false
% 31.42/4.50  --res_prop_simpl_given                  true
% 31.42/4.50  --res_passive_queue_type                priority_queues
% 31.42/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.42/4.50  --res_passive_queues_freq               [15;5]
% 31.42/4.50  --res_forward_subs                      full
% 31.42/4.50  --res_backward_subs                     full
% 31.42/4.50  --res_forward_subs_resolution           true
% 31.42/4.50  --res_backward_subs_resolution          true
% 31.42/4.50  --res_orphan_elimination                true
% 31.42/4.50  --res_time_limit                        2.
% 31.42/4.50  --res_out_proof                         true
% 31.42/4.50  
% 31.42/4.50  ------ Superposition Options
% 31.42/4.50  
% 31.42/4.50  --superposition_flag                    true
% 31.42/4.50  --sup_passive_queue_type                priority_queues
% 31.42/4.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.42/4.50  --sup_passive_queues_freq               [1;4]
% 31.42/4.50  --demod_completeness_check              fast
% 31.42/4.50  --demod_use_ground                      true
% 31.42/4.50  --sup_to_prop_solver                    passive
% 31.42/4.50  --sup_prop_simpl_new                    true
% 31.42/4.50  --sup_prop_simpl_given                  true
% 31.42/4.50  --sup_fun_splitting                     false
% 31.42/4.50  --sup_smt_interval                      50000
% 31.42/4.50  
% 31.42/4.50  ------ Superposition Simplification Setup
% 31.42/4.50  
% 31.42/4.50  --sup_indices_passive                   []
% 31.42/4.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.42/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_full_bw                           [BwDemod]
% 31.42/4.50  --sup_immed_triv                        [TrivRules]
% 31.42/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.42/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_immed_bw_main                     []
% 31.42/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.42/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.42/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.42/4.50  
% 31.42/4.50  ------ Combination Options
% 31.42/4.50  
% 31.42/4.50  --comb_res_mult                         3
% 31.42/4.50  --comb_sup_mult                         2
% 31.42/4.50  --comb_inst_mult                        10
% 31.42/4.50  
% 31.42/4.50  ------ Debug Options
% 31.42/4.50  
% 31.42/4.50  --dbg_backtrace                         false
% 31.42/4.50  --dbg_dump_prop_clauses                 false
% 31.42/4.50  --dbg_dump_prop_clauses_file            -
% 31.42/4.50  --dbg_out_stat                          false
% 31.42/4.50  ------ Parsing...
% 31.42/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.42/4.50  
% 31.42/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.42/4.50  
% 31.42/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.42/4.50  
% 31.42/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.42/4.50  ------ Proving...
% 31.42/4.50  ------ Problem Properties 
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  clauses                                 24
% 31.42/4.50  conjectures                             12
% 31.42/4.50  EPR                                     13
% 31.42/4.50  Horn                                    16
% 31.42/4.50  unary                                   12
% 31.42/4.50  binary                                  0
% 31.42/4.50  lits                                    94
% 31.42/4.50  lits eq                                 6
% 31.42/4.50  fd_pure                                 0
% 31.42/4.50  fd_pseudo                               0
% 31.42/4.50  fd_cond                                 0
% 31.42/4.50  fd_pseudo_cond                          1
% 31.42/4.50  AC symbols                              0
% 31.42/4.50  
% 31.42/4.50  ------ Input Options Time Limit: Unbounded
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  ------ 
% 31.42/4.50  Current options:
% 31.42/4.50  ------ 
% 31.42/4.50  
% 31.42/4.50  ------ Input Options
% 31.42/4.50  
% 31.42/4.50  --out_options                           all
% 31.42/4.50  --tptp_safe_out                         true
% 31.42/4.50  --problem_path                          ""
% 31.42/4.50  --include_path                          ""
% 31.42/4.50  --clausifier                            res/vclausify_rel
% 31.42/4.50  --clausifier_options                    --mode clausify
% 31.42/4.50  --stdin                                 false
% 31.42/4.50  --stats_out                             sel
% 31.42/4.50  
% 31.42/4.50  ------ General Options
% 31.42/4.50  
% 31.42/4.50  --fof                                   false
% 31.42/4.50  --time_out_real                         604.99
% 31.42/4.50  --time_out_virtual                      -1.
% 31.42/4.50  --symbol_type_check                     false
% 31.42/4.50  --clausify_out                          false
% 31.42/4.50  --sig_cnt_out                           false
% 31.42/4.50  --trig_cnt_out                          false
% 31.42/4.50  --trig_cnt_out_tolerance                1.
% 31.42/4.50  --trig_cnt_out_sk_spl                   false
% 31.42/4.50  --abstr_cl_out                          false
% 31.42/4.50  
% 31.42/4.50  ------ Global Options
% 31.42/4.50  
% 31.42/4.50  --schedule                              none
% 31.42/4.50  --add_important_lit                     false
% 31.42/4.50  --prop_solver_per_cl                    1000
% 31.42/4.50  --min_unsat_core                        false
% 31.42/4.50  --soft_assumptions                      false
% 31.42/4.50  --soft_lemma_size                       3
% 31.42/4.50  --prop_impl_unit_size                   0
% 31.42/4.50  --prop_impl_unit                        []
% 31.42/4.50  --share_sel_clauses                     true
% 31.42/4.50  --reset_solvers                         false
% 31.42/4.50  --bc_imp_inh                            [conj_cone]
% 31.42/4.50  --conj_cone_tolerance                   3.
% 31.42/4.50  --extra_neg_conj                        none
% 31.42/4.50  --large_theory_mode                     true
% 31.42/4.50  --prolific_symb_bound                   200
% 31.42/4.50  --lt_threshold                          2000
% 31.42/4.50  --clause_weak_htbl                      true
% 31.42/4.50  --gc_record_bc_elim                     false
% 31.42/4.50  
% 31.42/4.50  ------ Preprocessing Options
% 31.42/4.50  
% 31.42/4.50  --preprocessing_flag                    true
% 31.42/4.50  --time_out_prep_mult                    0.1
% 31.42/4.50  --splitting_mode                        input
% 31.42/4.50  --splitting_grd                         true
% 31.42/4.50  --splitting_cvd                         false
% 31.42/4.50  --splitting_cvd_svl                     false
% 31.42/4.50  --splitting_nvd                         32
% 31.42/4.50  --sub_typing                            true
% 31.42/4.50  --prep_gs_sim                           false
% 31.42/4.50  --prep_unflatten                        true
% 31.42/4.50  --prep_res_sim                          true
% 31.42/4.50  --prep_upred                            true
% 31.42/4.50  --prep_sem_filter                       exhaustive
% 31.42/4.50  --prep_sem_filter_out                   false
% 31.42/4.50  --pred_elim                             false
% 31.42/4.50  --res_sim_input                         true
% 31.42/4.50  --eq_ax_congr_red                       true
% 31.42/4.50  --pure_diseq_elim                       true
% 31.42/4.50  --brand_transform                       false
% 31.42/4.50  --non_eq_to_eq                          false
% 31.42/4.50  --prep_def_merge                        true
% 31.42/4.50  --prep_def_merge_prop_impl              false
% 31.42/4.50  --prep_def_merge_mbd                    true
% 31.42/4.50  --prep_def_merge_tr_red                 false
% 31.42/4.50  --prep_def_merge_tr_cl                  false
% 31.42/4.50  --smt_preprocessing                     true
% 31.42/4.50  --smt_ac_axioms                         fast
% 31.42/4.50  --preprocessed_out                      false
% 31.42/4.50  --preprocessed_stats                    false
% 31.42/4.50  
% 31.42/4.50  ------ Abstraction refinement Options
% 31.42/4.50  
% 31.42/4.50  --abstr_ref                             []
% 31.42/4.50  --abstr_ref_prep                        false
% 31.42/4.50  --abstr_ref_until_sat                   false
% 31.42/4.50  --abstr_ref_sig_restrict                funpre
% 31.42/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.42/4.50  --abstr_ref_under                       []
% 31.42/4.50  
% 31.42/4.50  ------ SAT Options
% 31.42/4.50  
% 31.42/4.50  --sat_mode                              false
% 31.42/4.50  --sat_fm_restart_options                ""
% 31.42/4.50  --sat_gr_def                            false
% 31.42/4.50  --sat_epr_types                         true
% 31.42/4.50  --sat_non_cyclic_types                  false
% 31.42/4.50  --sat_finite_models                     false
% 31.42/4.50  --sat_fm_lemmas                         false
% 31.42/4.50  --sat_fm_prep                           false
% 31.42/4.50  --sat_fm_uc_incr                        true
% 31.42/4.50  --sat_out_model                         small
% 31.42/4.50  --sat_out_clauses                       false
% 31.42/4.50  
% 31.42/4.50  ------ QBF Options
% 31.42/4.50  
% 31.42/4.50  --qbf_mode                              false
% 31.42/4.50  --qbf_elim_univ                         false
% 31.42/4.50  --qbf_dom_inst                          none
% 31.42/4.50  --qbf_dom_pre_inst                      false
% 31.42/4.50  --qbf_sk_in                             false
% 31.42/4.50  --qbf_pred_elim                         true
% 31.42/4.50  --qbf_split                             512
% 31.42/4.50  
% 31.42/4.50  ------ BMC1 Options
% 31.42/4.50  
% 31.42/4.50  --bmc1_incremental                      false
% 31.42/4.50  --bmc1_axioms                           reachable_all
% 31.42/4.50  --bmc1_min_bound                        0
% 31.42/4.50  --bmc1_max_bound                        -1
% 31.42/4.50  --bmc1_max_bound_default                -1
% 31.42/4.50  --bmc1_symbol_reachability              true
% 31.42/4.50  --bmc1_property_lemmas                  false
% 31.42/4.50  --bmc1_k_induction                      false
% 31.42/4.50  --bmc1_non_equiv_states                 false
% 31.42/4.50  --bmc1_deadlock                         false
% 31.42/4.50  --bmc1_ucm                              false
% 31.42/4.50  --bmc1_add_unsat_core                   none
% 31.42/4.50  --bmc1_unsat_core_children              false
% 31.42/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.42/4.50  --bmc1_out_stat                         full
% 31.42/4.50  --bmc1_ground_init                      false
% 31.42/4.50  --bmc1_pre_inst_next_state              false
% 31.42/4.50  --bmc1_pre_inst_state                   false
% 31.42/4.50  --bmc1_pre_inst_reach_state             false
% 31.42/4.50  --bmc1_out_unsat_core                   false
% 31.42/4.50  --bmc1_aig_witness_out                  false
% 31.42/4.50  --bmc1_verbose                          false
% 31.42/4.50  --bmc1_dump_clauses_tptp                false
% 31.42/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.42/4.50  --bmc1_dump_file                        -
% 31.42/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.42/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.42/4.50  --bmc1_ucm_extend_mode                  1
% 31.42/4.50  --bmc1_ucm_init_mode                    2
% 31.42/4.50  --bmc1_ucm_cone_mode                    none
% 31.42/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.42/4.50  --bmc1_ucm_relax_model                  4
% 31.42/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.42/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.42/4.50  --bmc1_ucm_layered_model                none
% 31.42/4.50  --bmc1_ucm_max_lemma_size               10
% 31.42/4.50  
% 31.42/4.50  ------ AIG Options
% 31.42/4.50  
% 31.42/4.50  --aig_mode                              false
% 31.42/4.50  
% 31.42/4.50  ------ Instantiation Options
% 31.42/4.50  
% 31.42/4.50  --instantiation_flag                    true
% 31.42/4.50  --inst_sos_flag                         false
% 31.42/4.50  --inst_sos_phase                        true
% 31.42/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.42/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.42/4.50  --inst_lit_sel_side                     num_symb
% 31.42/4.50  --inst_solver_per_active                1400
% 31.42/4.50  --inst_solver_calls_frac                1.
% 31.42/4.50  --inst_passive_queue_type               priority_queues
% 31.42/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.42/4.50  --inst_passive_queues_freq              [25;2]
% 31.42/4.50  --inst_dismatching                      true
% 31.42/4.50  --inst_eager_unprocessed_to_passive     true
% 31.42/4.50  --inst_prop_sim_given                   true
% 31.42/4.50  --inst_prop_sim_new                     false
% 31.42/4.50  --inst_subs_new                         false
% 31.42/4.50  --inst_eq_res_simp                      false
% 31.42/4.50  --inst_subs_given                       false
% 31.42/4.50  --inst_orphan_elimination               true
% 31.42/4.50  --inst_learning_loop_flag               true
% 31.42/4.50  --inst_learning_start                   3000
% 31.42/4.50  --inst_learning_factor                  2
% 31.42/4.50  --inst_start_prop_sim_after_learn       3
% 31.42/4.50  --inst_sel_renew                        solver
% 31.42/4.50  --inst_lit_activity_flag                true
% 31.42/4.50  --inst_restr_to_given                   false
% 31.42/4.50  --inst_activity_threshold               500
% 31.42/4.50  --inst_out_proof                        true
% 31.42/4.50  
% 31.42/4.50  ------ Resolution Options
% 31.42/4.50  
% 31.42/4.50  --resolution_flag                       true
% 31.42/4.50  --res_lit_sel                           adaptive
% 31.42/4.50  --res_lit_sel_side                      none
% 31.42/4.50  --res_ordering                          kbo
% 31.42/4.50  --res_to_prop_solver                    active
% 31.42/4.50  --res_prop_simpl_new                    false
% 31.42/4.50  --res_prop_simpl_given                  true
% 31.42/4.50  --res_passive_queue_type                priority_queues
% 31.42/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.42/4.50  --res_passive_queues_freq               [15;5]
% 31.42/4.50  --res_forward_subs                      full
% 31.42/4.50  --res_backward_subs                     full
% 31.42/4.50  --res_forward_subs_resolution           true
% 31.42/4.50  --res_backward_subs_resolution          true
% 31.42/4.50  --res_orphan_elimination                true
% 31.42/4.50  --res_time_limit                        2.
% 31.42/4.50  --res_out_proof                         true
% 31.42/4.50  
% 31.42/4.50  ------ Superposition Options
% 31.42/4.50  
% 31.42/4.50  --superposition_flag                    true
% 31.42/4.50  --sup_passive_queue_type                priority_queues
% 31.42/4.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.42/4.50  --sup_passive_queues_freq               [1;4]
% 31.42/4.50  --demod_completeness_check              fast
% 31.42/4.50  --demod_use_ground                      true
% 31.42/4.50  --sup_to_prop_solver                    passive
% 31.42/4.50  --sup_prop_simpl_new                    true
% 31.42/4.50  --sup_prop_simpl_given                  true
% 31.42/4.50  --sup_fun_splitting                     false
% 31.42/4.50  --sup_smt_interval                      50000
% 31.42/4.50  
% 31.42/4.50  ------ Superposition Simplification Setup
% 31.42/4.50  
% 31.42/4.50  --sup_indices_passive                   []
% 31.42/4.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.42/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.42/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_full_bw                           [BwDemod]
% 31.42/4.50  --sup_immed_triv                        [TrivRules]
% 31.42/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.42/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_immed_bw_main                     []
% 31.42/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.42/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.42/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.42/4.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.42/4.50  
% 31.42/4.50  ------ Combination Options
% 31.42/4.50  
% 31.42/4.50  --comb_res_mult                         3
% 31.42/4.50  --comb_sup_mult                         2
% 31.42/4.50  --comb_inst_mult                        10
% 31.42/4.50  
% 31.42/4.50  ------ Debug Options
% 31.42/4.50  
% 31.42/4.50  --dbg_backtrace                         false
% 31.42/4.50  --dbg_dump_prop_clauses                 false
% 31.42/4.50  --dbg_dump_prop_clauses_file            -
% 31.42/4.50  --dbg_out_stat                          false
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  ------ Proving...
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  % SZS status Theorem for theBenchmark.p
% 31.42/4.50  
% 31.42/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.42/4.50  
% 31.42/4.50  fof(f7,axiom,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f21,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f7])).
% 31.42/4.50  
% 31.42/4.50  fof(f22,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.42/4.50    inference(flattening,[],[f21])).
% 31.42/4.50  
% 31.42/4.50  fof(f27,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.42/4.50    inference(nnf_transformation,[],[f22])).
% 31.42/4.50  
% 31.42/4.50  fof(f43,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f27])).
% 31.42/4.50  
% 31.42/4.50  fof(f44,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f27])).
% 31.42/4.50  
% 31.42/4.50  fof(f8,conjecture,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f9,negated_conjecture,(
% 31.42/4.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 31.42/4.50    inference(negated_conjecture,[],[f8])).
% 31.42/4.50  
% 31.42/4.50  fof(f23,plain,(
% 31.42/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f9])).
% 31.42/4.50  
% 31.42/4.50  fof(f24,plain,(
% 31.42/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 31.42/4.50    inference(flattening,[],[f23])).
% 31.42/4.50  
% 31.42/4.50  fof(f31,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 31.42/4.50    introduced(choice_axiom,[])).
% 31.42/4.50  
% 31.42/4.50  fof(f30,plain,(
% 31.42/4.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 31.42/4.50    introduced(choice_axiom,[])).
% 31.42/4.50  
% 31.42/4.50  fof(f29,plain,(
% 31.42/4.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 31.42/4.50    introduced(choice_axiom,[])).
% 31.42/4.50  
% 31.42/4.50  fof(f28,plain,(
% 31.42/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 31.42/4.50    introduced(choice_axiom,[])).
% 31.42/4.50  
% 31.42/4.50  fof(f32,plain,(
% 31.42/4.50    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 31.42/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f31,f30,f29,f28])).
% 31.42/4.50  
% 31.42/4.50  fof(f49,plain,(
% 31.42/4.50    m1_pre_topc(sK1,sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f53,plain,(
% 31.42/4.50    m1_pre_topc(sK3,sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f3,axiom,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f13,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f3])).
% 31.42/4.50  
% 31.42/4.50  fof(f14,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(flattening,[],[f13])).
% 31.42/4.50  
% 31.42/4.50  fof(f25,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(nnf_transformation,[],[f14])).
% 31.42/4.50  
% 31.42/4.50  fof(f35,plain,(
% 31.42/4.50    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f25])).
% 31.42/4.50  
% 31.42/4.50  fof(f57,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(equality_resolution,[],[f35])).
% 31.42/4.50  
% 31.42/4.50  fof(f4,axiom,(
% 31.42/4.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f15,plain,(
% 31.42/4.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f4])).
% 31.42/4.50  
% 31.42/4.50  fof(f16,plain,(
% 31.42/4.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(flattening,[],[f15])).
% 31.42/4.50  
% 31.42/4.50  fof(f37,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f16])).
% 31.42/4.50  
% 31.42/4.50  fof(f38,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f16])).
% 31.42/4.50  
% 31.42/4.50  fof(f39,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f16])).
% 31.42/4.50  
% 31.42/4.50  fof(f45,plain,(
% 31.42/4.50    ~v2_struct_0(sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f47,plain,(
% 31.42/4.50    l1_pre_topc(sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f52,plain,(
% 31.42/4.50    ~v2_struct_0(sK3)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f54,plain,(
% 31.42/4.50    m1_pre_topc(sK1,sK2)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f55,plain,(
% 31.42/4.50    m1_pre_topc(sK3,sK2)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f50,plain,(
% 31.42/4.50    ~v2_struct_0(sK2)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f2,axiom,(
% 31.42/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f12,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 31.42/4.50    inference(ennf_transformation,[],[f2])).
% 31.42/4.50  
% 31.42/4.50  fof(f34,plain,(
% 31.42/4.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f12])).
% 31.42/4.50  
% 31.42/4.50  fof(f51,plain,(
% 31.42/4.50    m1_pre_topc(sK2,sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f48,plain,(
% 31.42/4.50    ~v2_struct_0(sK1)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f1,axiom,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f10,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f1])).
% 31.42/4.50  
% 31.42/4.50  fof(f11,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.42/4.50    inference(flattening,[],[f10])).
% 31.42/4.50  
% 31.42/4.50  fof(f33,plain,(
% 31.42/4.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f11])).
% 31.42/4.50  
% 31.42/4.50  fof(f5,axiom,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f17,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f5])).
% 31.42/4.50  
% 31.42/4.50  fof(f18,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(flattening,[],[f17])).
% 31.42/4.50  
% 31.42/4.50  fof(f26,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(nnf_transformation,[],[f18])).
% 31.42/4.50  
% 31.42/4.50  fof(f41,plain,(
% 31.42/4.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f26])).
% 31.42/4.50  
% 31.42/4.50  fof(f6,axiom,(
% 31.42/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 31.42/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.42/4.50  
% 31.42/4.50  fof(f19,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 31.42/4.50    inference(ennf_transformation,[],[f6])).
% 31.42/4.50  
% 31.42/4.50  fof(f20,plain,(
% 31.42/4.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 31.42/4.50    inference(flattening,[],[f19])).
% 31.42/4.50  
% 31.42/4.50  fof(f42,plain,(
% 31.42/4.50    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 31.42/4.50    inference(cnf_transformation,[],[f20])).
% 31.42/4.50  
% 31.42/4.50  fof(f56,plain,(
% 31.42/4.50    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  fof(f46,plain,(
% 31.42/4.50    v2_pre_topc(sK0)),
% 31.42/4.50    inference(cnf_transformation,[],[f32])).
% 31.42/4.50  
% 31.42/4.50  cnf(c_241,plain,
% 31.42/4.50      ( ~ r1_tarski(X0_44,X1_44)
% 31.42/4.50      | r1_tarski(X2_44,X3_44)
% 31.42/4.50      | X2_44 != X0_44
% 31.42/4.50      | X3_44 != X1_44 ),
% 31.42/4.50      theory(equality) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_86814,plain,
% 31.42/4.50      ( r1_tarski(X0_44,X1_44)
% 31.42/4.50      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 31.42/4.50      | X0_44 != u1_struct_0(X0_43)
% 31.42/4.50      | X1_44 != u1_struct_0(X1_43) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_241]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_87051,plain,
% 31.42/4.50      ( r1_tarski(X0_44,u1_struct_0(X0_43))
% 31.42/4.50      | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X0_43))
% 31.42/4.50      | X0_44 != u1_struct_0(X1_43)
% 31.42/4.50      | u1_struct_0(X0_43) != u1_struct_0(X0_43) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_86814]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_87248,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 31.42/4.50      | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X1_43))
% 31.42/4.50      | u1_struct_0(X1_43) != u1_struct_0(X1_43)
% 31.42/4.50      | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_87051]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_90032,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 31.42/4.50      | r1_tarski(u1_struct_0(k1_tsep_1(X1_43,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X1_43,sK1,sK3)) != u1_struct_0(X0_43)
% 31.42/4.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_87248]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_96652,plain,
% 31.42/4.50      ( r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 31.42/4.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_90032]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_96654,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 31.42/4.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_96652]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_228,plain,( X0_44 = X0_44 ),theory(equality) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_87052,plain,
% 31.42/4.50      ( u1_struct_0(X0_43) = u1_struct_0(X0_43) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_228]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_88280,plain,
% 31.42/4.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_87052]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_11,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 31.42/4.50      | ~ m1_pre_topc(X0,X2)
% 31.42/4.50      | ~ m1_pre_topc(X1,X2)
% 31.42/4.50      | m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ l1_pre_topc(X2)
% 31.42/4.50      | ~ v2_pre_topc(X2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f43]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_215,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 31.42/4.50      | ~ m1_pre_topc(X0_43,X2_43)
% 31.42/4.50      | ~ m1_pre_topc(X1_43,X2_43)
% 31.42/4.50      | m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ l1_pre_topc(X2_43)
% 31.42/4.50      | ~ v2_pre_topc(X2_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_11]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_12649,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 31.42/4.50      | m1_pre_topc(X0_43,sK2)
% 31.42/4.50      | ~ m1_pre_topc(X0_43,sK0)
% 31.42/4.50      | ~ m1_pre_topc(sK2,sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0)
% 31.42/4.50      | ~ v2_pre_topc(sK0) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_215]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_65366,plain,
% 31.42/4.50      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 31.42/4.50      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 31.42/4.50      | ~ m1_pre_topc(sK2,sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0)
% 31.42/4.50      | ~ v2_pre_topc(sK0) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_12649]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_10,plain,
% 31.42/4.50      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 31.42/4.50      | ~ m1_pre_topc(X0,X2)
% 31.42/4.50      | ~ m1_pre_topc(X1,X2)
% 31.42/4.50      | ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ l1_pre_topc(X2)
% 31.42/4.50      | ~ v2_pre_topc(X2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f44]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_216,plain,
% 31.42/4.50      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 31.42/4.50      | ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ m1_pre_topc(X0_43,X2_43)
% 31.42/4.50      | ~ m1_pre_topc(X1_43,X2_43)
% 31.42/4.50      | ~ l1_pre_topc(X2_43)
% 31.42/4.50      | ~ v2_pre_topc(X2_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_10]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1552,plain,
% 31.42/4.50      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 31.42/4.50      | ~ m1_pre_topc(X0_43,sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK2,sK2)
% 31.42/4.50      | ~ l1_pre_topc(sK2)
% 31.42/4.50      | ~ v2_pre_topc(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_216]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_6003,plain,
% 31.42/4.50      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 31.42/4.50      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK2,sK2)
% 31.42/4.50      | ~ l1_pre_topc(sK2)
% 31.42/4.50      | ~ v2_pre_topc(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_1552]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_19,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK1,sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_207,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK1,sK0) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_19]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_664,plain,
% 31.42/4.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_15,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK3,sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_211,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK3,sK0) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_15]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_660,plain,
% 31.42/4.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_3,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 31.42/4.50      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 31.42/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_6,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 31.42/4.50      | ~ l1_pre_topc(X1) ),
% 31.42/4.50      inference(cnf_transformation,[],[f37]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_5,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 31.42/4.50      | ~ l1_pre_topc(X1) ),
% 31.42/4.50      inference(cnf_transformation,[],[f38]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_4,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | ~ l1_pre_topc(X1) ),
% 31.42/4.50      inference(cnf_transformation,[],[f39]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_181,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 31.42/4.50      inference(global_propositional_subsumption,
% 31.42/4.50                [status(thm)],
% 31.42/4.50                [c_3,c_6,c_5,c_4]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_182,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 31.42/4.50      inference(renaming,[status(thm)],[c_181]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_202,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ m1_pre_topc(X2_43,X1_43)
% 31.42/4.50      | v2_struct_0(X1_43)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | v2_struct_0(X2_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43)
% 31.42/4.50      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_182]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_669,plain,
% 31.42/4.50      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 31.42/4.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 31.42/4.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 31.42/4.50      | v2_struct_0(X0_43) = iProver_top
% 31.42/4.50      | v2_struct_0(X1_43) = iProver_top
% 31.42/4.50      | v2_struct_0(X2_43) = iProver_top
% 31.42/4.50      | l1_pre_topc(X0_43) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_3397,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3))
% 31.42/4.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 31.42/4.50      | v2_struct_0(X0_43) = iProver_top
% 31.42/4.50      | v2_struct_0(sK3) = iProver_top
% 31.42/4.50      | v2_struct_0(sK0) = iProver_top
% 31.42/4.50      | l1_pre_topc(sK0) != iProver_top ),
% 31.42/4.50      inference(superposition,[status(thm)],[c_660,c_669]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_23,negated_conjecture,
% 31.42/4.50      ( ~ v2_struct_0(sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_24,plain,
% 31.42/4.50      ( v2_struct_0(sK0) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_21,negated_conjecture,
% 31.42/4.50      ( l1_pre_topc(sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_26,plain,
% 31.42/4.50      ( l1_pre_topc(sK0) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_16,negated_conjecture,
% 31.42/4.50      ( ~ v2_struct_0(sK3) ),
% 31.42/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_31,plain,
% 31.42/4.50      ( v2_struct_0(sK3) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_5132,plain,
% 31.42/4.50      ( v2_struct_0(X0_43) = iProver_top
% 31.42/4.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 31.42/4.50      | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3)) ),
% 31.42/4.50      inference(global_propositional_subsumption,
% 31.42/4.50                [status(thm)],
% 31.42/4.50                [c_3397,c_24,c_26,c_31]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_5133,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,X0_43,sK3))
% 31.42/4.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 31.42/4.50      | v2_struct_0(X0_43) = iProver_top ),
% 31.42/4.50      inference(renaming,[status(thm)],[c_5132]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_5143,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 31.42/4.50      | v2_struct_0(sK1) = iProver_top ),
% 31.42/4.50      inference(superposition,[status(thm)],[c_664,c_5133]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_14,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK1,sK2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_212,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK1,sK2) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_14]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_659,plain,
% 31.42/4.50      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_13,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK3,sK2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_213,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK3,sK2) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_13]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_658,plain,
% 31.42/4.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_3395,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3))
% 31.42/4.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 31.42/4.50      | v2_struct_0(X0_43) = iProver_top
% 31.42/4.50      | v2_struct_0(sK2) = iProver_top
% 31.42/4.50      | v2_struct_0(sK3) = iProver_top
% 31.42/4.50      | l1_pre_topc(sK2) != iProver_top ),
% 31.42/4.50      inference(superposition,[status(thm)],[c_658,c_669]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_18,negated_conjecture,
% 31.42/4.50      ( ~ v2_struct_0(sK2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_29,plain,
% 31.42/4.50      ( v2_struct_0(sK2) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f34]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_224,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43)
% 31.42/4.50      | l1_pre_topc(X0_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_1]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_17,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK2,sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_209,negated_conjecture,
% 31.42/4.50      ( m1_pre_topc(sK2,sK0) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_17]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1192,plain,
% 31.42/4.50      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 31.42/4.50      inference(resolution,[status(thm)],[c_224,c_209]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1193,plain,
% 31.42/4.50      ( l1_pre_topc(sK2) = iProver_top
% 31.42/4.50      | l1_pre_topc(sK0) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_4537,plain,
% 31.42/4.50      ( v2_struct_0(X0_43) = iProver_top
% 31.42/4.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 31.42/4.50      | k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3)) ),
% 31.42/4.50      inference(global_propositional_subsumption,
% 31.42/4.50                [status(thm)],
% 31.42/4.50                [c_3395,c_26,c_29,c_31,c_1193]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_4538,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,X0_43,sK3))
% 31.42/4.50      | m1_pre_topc(X0_43,sK2) != iProver_top
% 31.42/4.50      | v2_struct_0(X0_43) = iProver_top ),
% 31.42/4.50      inference(renaming,[status(thm)],[c_4537]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_4547,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 31.42/4.50      | v2_struct_0(sK1) = iProver_top ),
% 31.42/4.50      inference(superposition,[status(thm)],[c_659,c_4538]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_20,negated_conjecture,
% 31.42/4.50      ( ~ v2_struct_0(sK1) ),
% 31.42/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_27,plain,
% 31.42/4.50      ( v2_struct_0(sK1) != iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_4717,plain,
% 31.42/4.50      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 31.42/4.50      inference(global_propositional_subsumption,
% 31.42/4.50                [status(thm)],
% 31.42/4.50                [c_4547,c_27]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_5163,plain,
% 31.42/4.50      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 31.42/4.50      | v2_struct_0(sK1) = iProver_top ),
% 31.42/4.50      inference(demodulation,[status(thm)],[c_5143,c_4717]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_222,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ m1_pre_topc(X2_43,X1_43)
% 31.42/4.50      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 31.42/4.50      | v2_struct_0(X1_43)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | v2_struct_0(X2_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_4]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1061,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,sK0)
% 31.42/4.50      | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK3),sK0)
% 31.42/4.50      | ~ m1_pre_topc(sK3,sK0)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | v2_struct_0(sK3)
% 31.42/4.50      | v2_struct_0(sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_222]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1328,plain,
% 31.42/4.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 31.42/4.50      | ~ m1_pre_topc(sK3,sK0)
% 31.42/4.50      | ~ m1_pre_topc(sK1,sK0)
% 31.42/4.50      | v2_struct_0(sK3)
% 31.42/4.50      | v2_struct_0(sK1)
% 31.42/4.50      | v2_struct_0(sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_1061]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1051,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,sK2)
% 31.42/4.50      | m1_pre_topc(k1_tsep_1(sK2,X0_43,sK3),sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK3,sK2)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | v2_struct_0(sK2)
% 31.42/4.50      | v2_struct_0(sK3)
% 31.42/4.50      | ~ l1_pre_topc(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_222]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1313,plain,
% 31.42/4.50      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK3,sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK1,sK2)
% 31.42/4.50      | v2_struct_0(sK2)
% 31.42/4.50      | v2_struct_0(sK3)
% 31.42/4.50      | v2_struct_0(sK1)
% 31.42/4.50      | ~ l1_pre_topc(sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_1051]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_662,plain,
% 31.42/4.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_0,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | ~ v2_pre_topc(X1)
% 31.42/4.50      | v2_pre_topc(X0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f33]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_225,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43)
% 31.42/4.50      | ~ v2_pre_topc(X1_43)
% 31.42/4.50      | v2_pre_topc(X0_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_0]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_646,plain,
% 31.42/4.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 31.42/4.50      | l1_pre_topc(X1_43) != iProver_top
% 31.42/4.50      | v2_pre_topc(X1_43) != iProver_top
% 31.42/4.50      | v2_pre_topc(X0_43) = iProver_top ),
% 31.42/4.50      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1238,plain,
% 31.42/4.50      ( l1_pre_topc(sK0) != iProver_top
% 31.42/4.50      | v2_pre_topc(sK2) = iProver_top
% 31.42/4.50      | v2_pre_topc(sK0) != iProver_top ),
% 31.42/4.50      inference(superposition,[status(thm)],[c_662,c_646]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1250,plain,
% 31.42/4.50      ( ~ l1_pre_topc(sK0) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK0) ),
% 31.42/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_1238]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_7,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | ~ m1_pre_topc(X2,X1)
% 31.42/4.50      | m1_pre_topc(X0,X2)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | v2_struct_0(X2)
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | ~ v2_pre_topc(X1)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f41]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_219,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | ~ m1_pre_topc(X2_43,X1_43)
% 31.42/4.50      | m1_pre_topc(X0_43,X2_43)
% 31.42/4.50      | v2_struct_0(X1_43)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | v2_struct_0(X2_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43)
% 31.42/4.50      | ~ v2_pre_topc(X1_43)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43)) != k1_tsep_1(X1_43,X0_43,X2_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_7]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1218,plain,
% 31.42/4.50      ( m1_pre_topc(sK2,sK2)
% 31.42/4.50      | ~ m1_pre_topc(sK2,sK0)
% 31.42/4.50      | v2_struct_0(sK2)
% 31.42/4.50      | v2_struct_0(sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0)
% 31.42/4.50      | ~ v2_pre_topc(sK0)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_219]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_9,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0,X1)
% 31.42/4.50      | v2_struct_0(X1)
% 31.42/4.50      | v2_struct_0(X0)
% 31.42/4.50      | ~ l1_pre_topc(X1)
% 31.42/4.50      | ~ v2_pre_topc(X1)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_217,plain,
% 31.42/4.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 31.42/4.50      | v2_struct_0(X1_43)
% 31.42/4.50      | v2_struct_0(X0_43)
% 31.42/4.50      | ~ l1_pre_topc(X1_43)
% 31.42/4.50      | ~ v2_pre_topc(X1_43)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
% 31.42/4.50      inference(subtyping,[status(esa)],[c_9]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_1020,plain,
% 31.42/4.50      ( ~ m1_pre_topc(sK2,sK0)
% 31.42/4.50      | v2_struct_0(sK2)
% 31.42/4.50      | v2_struct_0(sK0)
% 31.42/4.50      | ~ l1_pre_topc(sK0)
% 31.42/4.50      | ~ v2_pre_topc(sK0)
% 31.42/4.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 31.42/4.50      inference(instantiation,[status(thm)],[c_217]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_12,negated_conjecture,
% 31.42/4.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 31.42/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(c_22,negated_conjecture,
% 31.42/4.50      ( v2_pre_topc(sK0) ),
% 31.42/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.42/4.50  
% 31.42/4.50  cnf(contradiction,plain,
% 31.42/4.50      ( $false ),
% 31.42/4.50      inference(minisat,
% 31.42/4.50                [status(thm)],
% 31.42/4.50                [c_96654,c_88280,c_65366,c_6003,c_5163,c_1328,c_1313,
% 31.42/4.50                 c_1250,c_1218,c_1192,c_1020,c_12,c_13,c_14,c_15,c_16,
% 31.42/4.50                 c_17,c_18,c_19,c_27,c_20,c_21,c_22,c_23]) ).
% 31.42/4.50  
% 31.42/4.50  
% 31.42/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.42/4.50  
% 31.42/4.50  ------                               Statistics
% 31.42/4.50  
% 31.42/4.50  ------ Selected
% 31.42/4.50  
% 31.42/4.50  total_time:                             3.938
% 31.42/4.50  
%------------------------------------------------------------------------------
