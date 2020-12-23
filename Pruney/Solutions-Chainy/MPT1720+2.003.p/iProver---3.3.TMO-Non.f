%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:07 EST 2020

% Result     : Timeout 59.33s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  153 ( 580 expanded)
%              Number of clauses        :   96 ( 148 expanded)
%              Number of leaves         :   15 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  728 (5536 expanded)
%              Number of equality atoms :  134 ( 171 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f32,f31,f30,f29])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

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
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

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

fof(f58,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
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
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_159494,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | X0_44 != u1_struct_0(X0_43)
    | X1_44 != u1_struct_0(X1_43) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_159947,plain,
    ( r1_tarski(X0_44,u1_struct_0(X0_43))
    | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X0_43))
    | X0_44 != u1_struct_0(X1_43)
    | u1_struct_0(X0_43) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_159494])).

cnf(c_161476,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X1_43))
    | u1_struct_0(X1_43) != u1_struct_0(X1_43)
    | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_159947])).

cnf(c_163578,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_161476])).

cnf(c_181302,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_163578])).

cnf(c_214731,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_181302])).

cnf(c_232,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_48990,plain,
    ( u1_struct_0(X0_43) = u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_150186,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_48990])).

cnf(c_10,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_220,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4683,plain,
    ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK2)
    | ~ m1_pre_topc(sK2,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_13609,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_43)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_4683])).

cnf(c_28306,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13609])).

cnf(c_11,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_219,plain,
    ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_15270,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_15272,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15270])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_215,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_664,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_211,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_668,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

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
    inference(cnf_transformation,[],[f58])).

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

cnf(c_185,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6,c_5])).

cnf(c_186,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_206,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_673,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_3333,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_673])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7368,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3333,c_24,c_26,c_27])).

cnf(c_7369,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_7368])).

cnf(c_7377,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_7369])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_217,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_662,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_216,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_663,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_3330,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_673])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_228,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_213,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1180,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_228,c_213])).

cnf(c_1181,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_6058,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3330,c_26,c_27,c_29,c_1181])).

cnf(c_6059,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_6058])).

cnf(c_6067,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_6059])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6530,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6067,c_31])).

cnf(c_7427,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7377,c_6530])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_222,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43))
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_657,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43)) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_666,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_221,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_658,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1614,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_658])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1010,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_4379,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_23,c_22,c_21,c_18,c_17,c_1010])).

cnf(c_2,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_227,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_652,plain,
    ( m1_pre_topc(X0_43,X1_43) = iProver_top
    | m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_4382,plain,
    ( m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(X0_43,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4379,c_652])).

cnf(c_4387,plain,
    ( m1_pre_topc(X0_43,sK2) = iProver_top
    | m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4382,c_26,c_1181])).

cnf(c_4388,plain,
    ( m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(X0_43,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4387])).

cnf(c_4395,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_4388])).

cnf(c_4423,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4395])).

cnf(c_225,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1051,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1379,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1041,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_43,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1364,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_229,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_650,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_1236,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_650])).

cnf(c_1248,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1236])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_214731,c_150186,c_28306,c_15272,c_7427,c_4423,c_1379,c_1364,c_1248,c_1180,c_12,c_13,c_14,c_15,c_31,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.33/7.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.33/7.99  
% 59.33/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.33/7.99  
% 59.33/7.99  ------  iProver source info
% 59.33/7.99  
% 59.33/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.33/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.33/7.99  git: non_committed_changes: false
% 59.33/7.99  git: last_make_outside_of_git: false
% 59.33/7.99  
% 59.33/7.99  ------ 
% 59.33/7.99  
% 59.33/7.99  ------ Input Options
% 59.33/7.99  
% 59.33/7.99  --out_options                           all
% 59.33/7.99  --tptp_safe_out                         true
% 59.33/7.99  --problem_path                          ""
% 59.33/7.99  --include_path                          ""
% 59.33/7.99  --clausifier                            res/vclausify_rel
% 59.33/7.99  --clausifier_options                    --mode clausify
% 59.33/7.99  --stdin                                 false
% 59.33/7.99  --stats_out                             sel
% 59.33/7.99  
% 59.33/7.99  ------ General Options
% 59.33/7.99  
% 59.33/7.99  --fof                                   false
% 59.33/7.99  --time_out_real                         604.99
% 59.33/7.99  --time_out_virtual                      -1.
% 59.33/7.99  --symbol_type_check                     false
% 59.33/7.99  --clausify_out                          false
% 59.33/7.99  --sig_cnt_out                           false
% 59.33/7.99  --trig_cnt_out                          false
% 59.33/7.99  --trig_cnt_out_tolerance                1.
% 59.33/7.99  --trig_cnt_out_sk_spl                   false
% 59.33/7.99  --abstr_cl_out                          false
% 59.33/7.99  
% 59.33/7.99  ------ Global Options
% 59.33/7.99  
% 59.33/7.99  --schedule                              none
% 59.33/7.99  --add_important_lit                     false
% 59.33/7.99  --prop_solver_per_cl                    1000
% 59.33/7.99  --min_unsat_core                        false
% 59.33/7.99  --soft_assumptions                      false
% 59.33/7.99  --soft_lemma_size                       3
% 59.33/7.99  --prop_impl_unit_size                   0
% 59.33/7.99  --prop_impl_unit                        []
% 59.33/7.99  --share_sel_clauses                     true
% 59.33/7.99  --reset_solvers                         false
% 59.33/7.99  --bc_imp_inh                            [conj_cone]
% 59.33/7.99  --conj_cone_tolerance                   3.
% 59.33/7.99  --extra_neg_conj                        none
% 59.33/7.99  --large_theory_mode                     true
% 59.33/7.99  --prolific_symb_bound                   200
% 59.33/7.99  --lt_threshold                          2000
% 59.33/7.99  --clause_weak_htbl                      true
% 59.33/7.99  --gc_record_bc_elim                     false
% 59.33/7.99  
% 59.33/7.99  ------ Preprocessing Options
% 59.33/7.99  
% 59.33/7.99  --preprocessing_flag                    true
% 59.33/7.99  --time_out_prep_mult                    0.1
% 59.33/7.99  --splitting_mode                        input
% 59.33/7.99  --splitting_grd                         true
% 59.33/7.99  --splitting_cvd                         false
% 59.33/7.99  --splitting_cvd_svl                     false
% 59.33/7.99  --splitting_nvd                         32
% 59.33/7.99  --sub_typing                            true
% 59.33/7.99  --prep_gs_sim                           false
% 59.33/7.99  --prep_unflatten                        true
% 59.33/7.99  --prep_res_sim                          true
% 59.33/7.99  --prep_upred                            true
% 59.33/7.99  --prep_sem_filter                       exhaustive
% 59.33/7.99  --prep_sem_filter_out                   false
% 59.33/7.99  --pred_elim                             false
% 59.33/7.99  --res_sim_input                         true
% 59.33/7.99  --eq_ax_congr_red                       true
% 59.33/7.99  --pure_diseq_elim                       true
% 59.33/7.99  --brand_transform                       false
% 59.33/7.99  --non_eq_to_eq                          false
% 59.33/7.99  --prep_def_merge                        true
% 59.33/7.99  --prep_def_merge_prop_impl              false
% 59.33/7.99  --prep_def_merge_mbd                    true
% 59.33/7.99  --prep_def_merge_tr_red                 false
% 59.33/7.99  --prep_def_merge_tr_cl                  false
% 59.33/7.99  --smt_preprocessing                     true
% 59.33/7.99  --smt_ac_axioms                         fast
% 59.33/7.99  --preprocessed_out                      false
% 59.33/7.99  --preprocessed_stats                    false
% 59.33/7.99  
% 59.33/7.99  ------ Abstraction refinement Options
% 59.33/7.99  
% 59.33/7.99  --abstr_ref                             []
% 59.33/7.99  --abstr_ref_prep                        false
% 59.33/7.99  --abstr_ref_until_sat                   false
% 59.33/7.99  --abstr_ref_sig_restrict                funpre
% 59.33/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.33/7.99  --abstr_ref_under                       []
% 59.33/7.99  
% 59.33/7.99  ------ SAT Options
% 59.33/7.99  
% 59.33/7.99  --sat_mode                              false
% 59.33/7.99  --sat_fm_restart_options                ""
% 59.33/7.99  --sat_gr_def                            false
% 59.33/7.99  --sat_epr_types                         true
% 59.33/7.99  --sat_non_cyclic_types                  false
% 59.33/7.99  --sat_finite_models                     false
% 59.33/7.99  --sat_fm_lemmas                         false
% 59.33/7.99  --sat_fm_prep                           false
% 59.33/7.99  --sat_fm_uc_incr                        true
% 59.33/7.99  --sat_out_model                         small
% 59.33/7.99  --sat_out_clauses                       false
% 59.33/7.99  
% 59.33/7.99  ------ QBF Options
% 59.33/7.99  
% 59.33/7.99  --qbf_mode                              false
% 59.33/7.99  --qbf_elim_univ                         false
% 59.33/7.99  --qbf_dom_inst                          none
% 59.33/7.99  --qbf_dom_pre_inst                      false
% 59.33/7.99  --qbf_sk_in                             false
% 59.33/7.99  --qbf_pred_elim                         true
% 59.33/7.99  --qbf_split                             512
% 59.33/7.99  
% 59.33/7.99  ------ BMC1 Options
% 59.33/7.99  
% 59.33/7.99  --bmc1_incremental                      false
% 59.33/7.99  --bmc1_axioms                           reachable_all
% 59.33/7.99  --bmc1_min_bound                        0
% 59.33/7.99  --bmc1_max_bound                        -1
% 59.33/7.99  --bmc1_max_bound_default                -1
% 59.33/7.99  --bmc1_symbol_reachability              true
% 59.33/7.99  --bmc1_property_lemmas                  false
% 59.33/7.99  --bmc1_k_induction                      false
% 59.33/7.99  --bmc1_non_equiv_states                 false
% 59.33/7.99  --bmc1_deadlock                         false
% 59.33/7.99  --bmc1_ucm                              false
% 59.33/7.99  --bmc1_add_unsat_core                   none
% 59.33/7.99  --bmc1_unsat_core_children              false
% 59.33/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.33/7.99  --bmc1_out_stat                         full
% 59.33/7.99  --bmc1_ground_init                      false
% 59.33/7.99  --bmc1_pre_inst_next_state              false
% 59.33/7.99  --bmc1_pre_inst_state                   false
% 59.33/7.99  --bmc1_pre_inst_reach_state             false
% 59.33/7.99  --bmc1_out_unsat_core                   false
% 59.33/7.99  --bmc1_aig_witness_out                  false
% 59.33/7.99  --bmc1_verbose                          false
% 59.33/7.99  --bmc1_dump_clauses_tptp                false
% 59.33/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.33/7.99  --bmc1_dump_file                        -
% 59.33/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.33/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.33/7.99  --bmc1_ucm_extend_mode                  1
% 59.33/7.99  --bmc1_ucm_init_mode                    2
% 59.33/7.99  --bmc1_ucm_cone_mode                    none
% 59.33/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.33/7.99  --bmc1_ucm_relax_model                  4
% 59.33/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.33/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.33/7.99  --bmc1_ucm_layered_model                none
% 59.33/7.99  --bmc1_ucm_max_lemma_size               10
% 59.33/7.99  
% 59.33/7.99  ------ AIG Options
% 59.33/7.99  
% 59.33/7.99  --aig_mode                              false
% 59.33/7.99  
% 59.33/7.99  ------ Instantiation Options
% 59.33/7.99  
% 59.33/7.99  --instantiation_flag                    true
% 59.33/7.99  --inst_sos_flag                         false
% 59.33/7.99  --inst_sos_phase                        true
% 59.33/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.33/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.33/7.99  --inst_lit_sel_side                     num_symb
% 59.33/7.99  --inst_solver_per_active                1400
% 59.33/7.99  --inst_solver_calls_frac                1.
% 59.33/7.99  --inst_passive_queue_type               priority_queues
% 59.33/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.33/7.99  --inst_passive_queues_freq              [25;2]
% 59.33/7.99  --inst_dismatching                      true
% 59.33/7.99  --inst_eager_unprocessed_to_passive     true
% 59.33/7.99  --inst_prop_sim_given                   true
% 59.33/7.99  --inst_prop_sim_new                     false
% 59.33/7.99  --inst_subs_new                         false
% 59.33/7.99  --inst_eq_res_simp                      false
% 59.33/7.99  --inst_subs_given                       false
% 59.33/7.99  --inst_orphan_elimination               true
% 59.33/7.99  --inst_learning_loop_flag               true
% 59.33/7.99  --inst_learning_start                   3000
% 59.33/7.99  --inst_learning_factor                  2
% 59.33/7.99  --inst_start_prop_sim_after_learn       3
% 59.33/7.99  --inst_sel_renew                        solver
% 59.33/7.99  --inst_lit_activity_flag                true
% 59.33/7.99  --inst_restr_to_given                   false
% 59.33/7.99  --inst_activity_threshold               500
% 59.33/7.99  --inst_out_proof                        true
% 59.33/7.99  
% 59.33/7.99  ------ Resolution Options
% 59.33/7.99  
% 59.33/7.99  --resolution_flag                       true
% 59.33/7.99  --res_lit_sel                           adaptive
% 59.33/7.99  --res_lit_sel_side                      none
% 59.33/7.99  --res_ordering                          kbo
% 59.33/7.99  --res_to_prop_solver                    active
% 59.33/7.99  --res_prop_simpl_new                    false
% 59.33/7.99  --res_prop_simpl_given                  true
% 59.33/7.99  --res_passive_queue_type                priority_queues
% 59.33/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.33/7.99  --res_passive_queues_freq               [15;5]
% 59.33/7.99  --res_forward_subs                      full
% 59.33/7.99  --res_backward_subs                     full
% 59.33/7.99  --res_forward_subs_resolution           true
% 59.33/7.99  --res_backward_subs_resolution          true
% 59.33/7.99  --res_orphan_elimination                true
% 59.33/7.99  --res_time_limit                        2.
% 59.33/7.99  --res_out_proof                         true
% 59.33/7.99  
% 59.33/7.99  ------ Superposition Options
% 59.33/7.99  
% 59.33/7.99  --superposition_flag                    true
% 59.33/7.99  --sup_passive_queue_type                priority_queues
% 59.33/7.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.33/7.99  --sup_passive_queues_freq               [1;4]
% 59.33/7.99  --demod_completeness_check              fast
% 59.33/7.99  --demod_use_ground                      true
% 59.33/7.99  --sup_to_prop_solver                    passive
% 59.33/7.99  --sup_prop_simpl_new                    true
% 59.33/7.99  --sup_prop_simpl_given                  true
% 59.33/7.99  --sup_fun_splitting                     false
% 59.33/7.99  --sup_smt_interval                      50000
% 59.33/7.99  
% 59.33/7.99  ------ Superposition Simplification Setup
% 59.33/7.99  
% 59.33/7.99  --sup_indices_passive                   []
% 59.33/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.33/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_full_bw                           [BwDemod]
% 59.33/7.99  --sup_immed_triv                        [TrivRules]
% 59.33/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.33/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_immed_bw_main                     []
% 59.33/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.33/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.33/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.33/7.99  
% 59.33/7.99  ------ Combination Options
% 59.33/7.99  
% 59.33/7.99  --comb_res_mult                         3
% 59.33/7.99  --comb_sup_mult                         2
% 59.33/7.99  --comb_inst_mult                        10
% 59.33/7.99  
% 59.33/7.99  ------ Debug Options
% 59.33/7.99  
% 59.33/7.99  --dbg_backtrace                         false
% 59.33/7.99  --dbg_dump_prop_clauses                 false
% 59.33/7.99  --dbg_dump_prop_clauses_file            -
% 59.33/7.99  --dbg_out_stat                          false
% 59.33/7.99  ------ Parsing...
% 59.33/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.33/7.99  
% 59.33/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 59.33/7.99  
% 59.33/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.33/7.99  
% 59.33/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.33/7.99  ------ Proving...
% 59.33/7.99  ------ Problem Properties 
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  clauses                                 24
% 59.33/7.99  conjectures                             12
% 59.33/7.99  EPR                                     13
% 59.33/7.99  Horn                                    17
% 59.33/7.99  unary                                   12
% 59.33/7.99  binary                                  0
% 59.33/7.99  lits                                    87
% 59.33/7.99  lits eq                                 4
% 59.33/7.99  fd_pure                                 0
% 59.33/7.99  fd_pseudo                               0
% 59.33/7.99  fd_cond                                 0
% 59.33/7.99  fd_pseudo_cond                          1
% 59.33/7.99  AC symbols                              0
% 59.33/7.99  
% 59.33/7.99  ------ Input Options Time Limit: Unbounded
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  ------ 
% 59.33/7.99  Current options:
% 59.33/7.99  ------ 
% 59.33/7.99  
% 59.33/7.99  ------ Input Options
% 59.33/7.99  
% 59.33/7.99  --out_options                           all
% 59.33/7.99  --tptp_safe_out                         true
% 59.33/7.99  --problem_path                          ""
% 59.33/7.99  --include_path                          ""
% 59.33/7.99  --clausifier                            res/vclausify_rel
% 59.33/7.99  --clausifier_options                    --mode clausify
% 59.33/7.99  --stdin                                 false
% 59.33/7.99  --stats_out                             sel
% 59.33/7.99  
% 59.33/7.99  ------ General Options
% 59.33/7.99  
% 59.33/7.99  --fof                                   false
% 59.33/7.99  --time_out_real                         604.99
% 59.33/7.99  --time_out_virtual                      -1.
% 59.33/7.99  --symbol_type_check                     false
% 59.33/7.99  --clausify_out                          false
% 59.33/7.99  --sig_cnt_out                           false
% 59.33/7.99  --trig_cnt_out                          false
% 59.33/7.99  --trig_cnt_out_tolerance                1.
% 59.33/7.99  --trig_cnt_out_sk_spl                   false
% 59.33/7.99  --abstr_cl_out                          false
% 59.33/7.99  
% 59.33/7.99  ------ Global Options
% 59.33/7.99  
% 59.33/7.99  --schedule                              none
% 59.33/7.99  --add_important_lit                     false
% 59.33/7.99  --prop_solver_per_cl                    1000
% 59.33/7.99  --min_unsat_core                        false
% 59.33/7.99  --soft_assumptions                      false
% 59.33/7.99  --soft_lemma_size                       3
% 59.33/7.99  --prop_impl_unit_size                   0
% 59.33/7.99  --prop_impl_unit                        []
% 59.33/7.99  --share_sel_clauses                     true
% 59.33/7.99  --reset_solvers                         false
% 59.33/7.99  --bc_imp_inh                            [conj_cone]
% 59.33/7.99  --conj_cone_tolerance                   3.
% 59.33/7.99  --extra_neg_conj                        none
% 59.33/7.99  --large_theory_mode                     true
% 59.33/7.99  --prolific_symb_bound                   200
% 59.33/7.99  --lt_threshold                          2000
% 59.33/7.99  --clause_weak_htbl                      true
% 59.33/7.99  --gc_record_bc_elim                     false
% 59.33/7.99  
% 59.33/7.99  ------ Preprocessing Options
% 59.33/7.99  
% 59.33/7.99  --preprocessing_flag                    true
% 59.33/7.99  --time_out_prep_mult                    0.1
% 59.33/7.99  --splitting_mode                        input
% 59.33/7.99  --splitting_grd                         true
% 59.33/7.99  --splitting_cvd                         false
% 59.33/7.99  --splitting_cvd_svl                     false
% 59.33/7.99  --splitting_nvd                         32
% 59.33/7.99  --sub_typing                            true
% 59.33/7.99  --prep_gs_sim                           false
% 59.33/7.99  --prep_unflatten                        true
% 59.33/7.99  --prep_res_sim                          true
% 59.33/7.99  --prep_upred                            true
% 59.33/7.99  --prep_sem_filter                       exhaustive
% 59.33/7.99  --prep_sem_filter_out                   false
% 59.33/7.99  --pred_elim                             false
% 59.33/7.99  --res_sim_input                         true
% 59.33/7.99  --eq_ax_congr_red                       true
% 59.33/7.99  --pure_diseq_elim                       true
% 59.33/7.99  --brand_transform                       false
% 59.33/7.99  --non_eq_to_eq                          false
% 59.33/7.99  --prep_def_merge                        true
% 59.33/7.99  --prep_def_merge_prop_impl              false
% 59.33/7.99  --prep_def_merge_mbd                    true
% 59.33/7.99  --prep_def_merge_tr_red                 false
% 59.33/7.99  --prep_def_merge_tr_cl                  false
% 59.33/7.99  --smt_preprocessing                     true
% 59.33/7.99  --smt_ac_axioms                         fast
% 59.33/7.99  --preprocessed_out                      false
% 59.33/7.99  --preprocessed_stats                    false
% 59.33/7.99  
% 59.33/7.99  ------ Abstraction refinement Options
% 59.33/7.99  
% 59.33/7.99  --abstr_ref                             []
% 59.33/7.99  --abstr_ref_prep                        false
% 59.33/7.99  --abstr_ref_until_sat                   false
% 59.33/7.99  --abstr_ref_sig_restrict                funpre
% 59.33/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.33/7.99  --abstr_ref_under                       []
% 59.33/7.99  
% 59.33/7.99  ------ SAT Options
% 59.33/7.99  
% 59.33/7.99  --sat_mode                              false
% 59.33/7.99  --sat_fm_restart_options                ""
% 59.33/7.99  --sat_gr_def                            false
% 59.33/7.99  --sat_epr_types                         true
% 59.33/7.99  --sat_non_cyclic_types                  false
% 59.33/7.99  --sat_finite_models                     false
% 59.33/7.99  --sat_fm_lemmas                         false
% 59.33/7.99  --sat_fm_prep                           false
% 59.33/7.99  --sat_fm_uc_incr                        true
% 59.33/7.99  --sat_out_model                         small
% 59.33/7.99  --sat_out_clauses                       false
% 59.33/7.99  
% 59.33/7.99  ------ QBF Options
% 59.33/7.99  
% 59.33/7.99  --qbf_mode                              false
% 59.33/7.99  --qbf_elim_univ                         false
% 59.33/7.99  --qbf_dom_inst                          none
% 59.33/7.99  --qbf_dom_pre_inst                      false
% 59.33/7.99  --qbf_sk_in                             false
% 59.33/7.99  --qbf_pred_elim                         true
% 59.33/7.99  --qbf_split                             512
% 59.33/7.99  
% 59.33/7.99  ------ BMC1 Options
% 59.33/7.99  
% 59.33/7.99  --bmc1_incremental                      false
% 59.33/7.99  --bmc1_axioms                           reachable_all
% 59.33/7.99  --bmc1_min_bound                        0
% 59.33/7.99  --bmc1_max_bound                        -1
% 59.33/7.99  --bmc1_max_bound_default                -1
% 59.33/7.99  --bmc1_symbol_reachability              true
% 59.33/7.99  --bmc1_property_lemmas                  false
% 59.33/7.99  --bmc1_k_induction                      false
% 59.33/7.99  --bmc1_non_equiv_states                 false
% 59.33/7.99  --bmc1_deadlock                         false
% 59.33/7.99  --bmc1_ucm                              false
% 59.33/7.99  --bmc1_add_unsat_core                   none
% 59.33/7.99  --bmc1_unsat_core_children              false
% 59.33/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.33/7.99  --bmc1_out_stat                         full
% 59.33/7.99  --bmc1_ground_init                      false
% 59.33/7.99  --bmc1_pre_inst_next_state              false
% 59.33/7.99  --bmc1_pre_inst_state                   false
% 59.33/7.99  --bmc1_pre_inst_reach_state             false
% 59.33/7.99  --bmc1_out_unsat_core                   false
% 59.33/7.99  --bmc1_aig_witness_out                  false
% 59.33/7.99  --bmc1_verbose                          false
% 59.33/7.99  --bmc1_dump_clauses_tptp                false
% 59.33/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.33/7.99  --bmc1_dump_file                        -
% 59.33/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.33/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.33/7.99  --bmc1_ucm_extend_mode                  1
% 59.33/7.99  --bmc1_ucm_init_mode                    2
% 59.33/7.99  --bmc1_ucm_cone_mode                    none
% 59.33/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.33/7.99  --bmc1_ucm_relax_model                  4
% 59.33/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.33/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.33/7.99  --bmc1_ucm_layered_model                none
% 59.33/7.99  --bmc1_ucm_max_lemma_size               10
% 59.33/7.99  
% 59.33/7.99  ------ AIG Options
% 59.33/7.99  
% 59.33/7.99  --aig_mode                              false
% 59.33/7.99  
% 59.33/7.99  ------ Instantiation Options
% 59.33/7.99  
% 59.33/7.99  --instantiation_flag                    true
% 59.33/7.99  --inst_sos_flag                         false
% 59.33/7.99  --inst_sos_phase                        true
% 59.33/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.33/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.33/7.99  --inst_lit_sel_side                     num_symb
% 59.33/7.99  --inst_solver_per_active                1400
% 59.33/7.99  --inst_solver_calls_frac                1.
% 59.33/7.99  --inst_passive_queue_type               priority_queues
% 59.33/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.33/7.99  --inst_passive_queues_freq              [25;2]
% 59.33/7.99  --inst_dismatching                      true
% 59.33/7.99  --inst_eager_unprocessed_to_passive     true
% 59.33/7.99  --inst_prop_sim_given                   true
% 59.33/7.99  --inst_prop_sim_new                     false
% 59.33/7.99  --inst_subs_new                         false
% 59.33/7.99  --inst_eq_res_simp                      false
% 59.33/7.99  --inst_subs_given                       false
% 59.33/7.99  --inst_orphan_elimination               true
% 59.33/7.99  --inst_learning_loop_flag               true
% 59.33/7.99  --inst_learning_start                   3000
% 59.33/7.99  --inst_learning_factor                  2
% 59.33/7.99  --inst_start_prop_sim_after_learn       3
% 59.33/7.99  --inst_sel_renew                        solver
% 59.33/7.99  --inst_lit_activity_flag                true
% 59.33/7.99  --inst_restr_to_given                   false
% 59.33/7.99  --inst_activity_threshold               500
% 59.33/7.99  --inst_out_proof                        true
% 59.33/7.99  
% 59.33/7.99  ------ Resolution Options
% 59.33/7.99  
% 59.33/7.99  --resolution_flag                       true
% 59.33/7.99  --res_lit_sel                           adaptive
% 59.33/7.99  --res_lit_sel_side                      none
% 59.33/7.99  --res_ordering                          kbo
% 59.33/7.99  --res_to_prop_solver                    active
% 59.33/7.99  --res_prop_simpl_new                    false
% 59.33/7.99  --res_prop_simpl_given                  true
% 59.33/7.99  --res_passive_queue_type                priority_queues
% 59.33/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.33/7.99  --res_passive_queues_freq               [15;5]
% 59.33/7.99  --res_forward_subs                      full
% 59.33/7.99  --res_backward_subs                     full
% 59.33/7.99  --res_forward_subs_resolution           true
% 59.33/7.99  --res_backward_subs_resolution          true
% 59.33/7.99  --res_orphan_elimination                true
% 59.33/7.99  --res_time_limit                        2.
% 59.33/7.99  --res_out_proof                         true
% 59.33/7.99  
% 59.33/7.99  ------ Superposition Options
% 59.33/7.99  
% 59.33/7.99  --superposition_flag                    true
% 59.33/7.99  --sup_passive_queue_type                priority_queues
% 59.33/7.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.33/7.99  --sup_passive_queues_freq               [1;4]
% 59.33/7.99  --demod_completeness_check              fast
% 59.33/7.99  --demod_use_ground                      true
% 59.33/7.99  --sup_to_prop_solver                    passive
% 59.33/7.99  --sup_prop_simpl_new                    true
% 59.33/7.99  --sup_prop_simpl_given                  true
% 59.33/7.99  --sup_fun_splitting                     false
% 59.33/7.99  --sup_smt_interval                      50000
% 59.33/7.99  
% 59.33/7.99  ------ Superposition Simplification Setup
% 59.33/7.99  
% 59.33/7.99  --sup_indices_passive                   []
% 59.33/7.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.33/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.33/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_full_bw                           [BwDemod]
% 59.33/7.99  --sup_immed_triv                        [TrivRules]
% 59.33/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.33/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_immed_bw_main                     []
% 59.33/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.33/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.33/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.33/7.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.33/7.99  
% 59.33/7.99  ------ Combination Options
% 59.33/7.99  
% 59.33/7.99  --comb_res_mult                         3
% 59.33/7.99  --comb_sup_mult                         2
% 59.33/7.99  --comb_inst_mult                        10
% 59.33/7.99  
% 59.33/7.99  ------ Debug Options
% 59.33/7.99  
% 59.33/7.99  --dbg_backtrace                         false
% 59.33/7.99  --dbg_dump_prop_clauses                 false
% 59.33/7.99  --dbg_dump_prop_clauses_file            -
% 59.33/7.99  --dbg_out_stat                          false
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  ------ Proving...
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  % SZS status Theorem for theBenchmark.p
% 59.33/7.99  
% 59.33/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.33/7.99  
% 59.33/7.99  fof(f8,axiom,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f23,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f8])).
% 59.33/7.99  
% 59.33/7.99  fof(f24,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 59.33/7.99    inference(flattening,[],[f23])).
% 59.33/7.99  
% 59.33/7.99  fof(f28,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 59.33/7.99    inference(nnf_transformation,[],[f24])).
% 59.33/7.99  
% 59.33/7.99  fof(f45,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f28])).
% 59.33/7.99  
% 59.33/7.99  fof(f44,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f28])).
% 59.33/7.99  
% 59.33/7.99  fof(f9,conjecture,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f10,negated_conjecture,(
% 59.33/7.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 59.33/7.99    inference(negated_conjecture,[],[f9])).
% 59.33/7.99  
% 59.33/7.99  fof(f25,plain,(
% 59.33/7.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f10])).
% 59.33/7.99  
% 59.33/7.99  fof(f26,plain,(
% 59.33/7.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 59.33/7.99    inference(flattening,[],[f25])).
% 59.33/7.99  
% 59.33/7.99  fof(f32,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 59.33/7.99    introduced(choice_axiom,[])).
% 59.33/7.99  
% 59.33/7.99  fof(f31,plain,(
% 59.33/7.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 59.33/7.99    introduced(choice_axiom,[])).
% 59.33/7.99  
% 59.33/7.99  fof(f30,plain,(
% 59.33/7.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 59.33/7.99    introduced(choice_axiom,[])).
% 59.33/7.99  
% 59.33/7.99  fof(f29,plain,(
% 59.33/7.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 59.33/7.99    introduced(choice_axiom,[])).
% 59.33/7.99  
% 59.33/7.99  fof(f33,plain,(
% 59.33/7.99    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 59.33/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f32,f31,f30,f29])).
% 59.33/7.99  
% 59.33/7.99  fof(f54,plain,(
% 59.33/7.99    m1_pre_topc(sK3,sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f50,plain,(
% 59.33/7.99    m1_pre_topc(sK1,sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f4,axiom,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f15,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f4])).
% 59.33/7.99  
% 59.33/7.99  fof(f16,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 59.33/7.99    inference(flattening,[],[f15])).
% 59.33/7.99  
% 59.33/7.99  fof(f27,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 59.33/7.99    inference(nnf_transformation,[],[f16])).
% 59.33/7.99  
% 59.33/7.99  fof(f37,plain,(
% 59.33/7.99    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f27])).
% 59.33/7.99  
% 59.33/7.99  fof(f58,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(equality_resolution,[],[f37])).
% 59.33/7.99  
% 59.33/7.99  fof(f5,axiom,(
% 59.33/7.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f17,plain,(
% 59.33/7.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f5])).
% 59.33/7.99  
% 59.33/7.99  fof(f18,plain,(
% 59.33/7.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 59.33/7.99    inference(flattening,[],[f17])).
% 59.33/7.99  
% 59.33/7.99  fof(f39,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f18])).
% 59.33/7.99  
% 59.33/7.99  fof(f40,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f18])).
% 59.33/7.99  
% 59.33/7.99  fof(f41,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f18])).
% 59.33/7.99  
% 59.33/7.99  fof(f46,plain,(
% 59.33/7.99    ~v2_struct_0(sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f48,plain,(
% 59.33/7.99    l1_pre_topc(sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f49,plain,(
% 59.33/7.99    ~v2_struct_0(sK1)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f56,plain,(
% 59.33/7.99    m1_pre_topc(sK3,sK2)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f55,plain,(
% 59.33/7.99    m1_pre_topc(sK1,sK2)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f51,plain,(
% 59.33/7.99    ~v2_struct_0(sK2)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f2,axiom,(
% 59.33/7.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f13,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 59.33/7.99    inference(ennf_transformation,[],[f2])).
% 59.33/7.99  
% 59.33/7.99  fof(f35,plain,(
% 59.33/7.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f13])).
% 59.33/7.99  
% 59.33/7.99  fof(f52,plain,(
% 59.33/7.99    m1_pre_topc(sK2,sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f53,plain,(
% 59.33/7.99    ~v2_struct_0(sK3)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f6,axiom,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f19,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f6])).
% 59.33/7.99  
% 59.33/7.99  fof(f20,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 59.33/7.99    inference(flattening,[],[f19])).
% 59.33/7.99  
% 59.33/7.99  fof(f42,plain,(
% 59.33/7.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f20])).
% 59.33/7.99  
% 59.33/7.99  fof(f7,axiom,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f21,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f7])).
% 59.33/7.99  
% 59.33/7.99  fof(f22,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 59.33/7.99    inference(flattening,[],[f21])).
% 59.33/7.99  
% 59.33/7.99  fof(f43,plain,(
% 59.33/7.99    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f22])).
% 59.33/7.99  
% 59.33/7.99  fof(f47,plain,(
% 59.33/7.99    v2_pre_topc(sK0)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  fof(f3,axiom,(
% 59.33/7.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f14,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 59.33/7.99    inference(ennf_transformation,[],[f3])).
% 59.33/7.99  
% 59.33/7.99  fof(f36,plain,(
% 59.33/7.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f14])).
% 59.33/7.99  
% 59.33/7.99  fof(f1,axiom,(
% 59.33/7.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 59.33/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.33/7.99  
% 59.33/7.99  fof(f11,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 59.33/7.99    inference(ennf_transformation,[],[f1])).
% 59.33/7.99  
% 59.33/7.99  fof(f12,plain,(
% 59.33/7.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 59.33/7.99    inference(flattening,[],[f11])).
% 59.33/7.99  
% 59.33/7.99  fof(f34,plain,(
% 59.33/7.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 59.33/7.99    inference(cnf_transformation,[],[f12])).
% 59.33/7.99  
% 59.33/7.99  fof(f57,plain,(
% 59.33/7.99    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 59.33/7.99    inference(cnf_transformation,[],[f33])).
% 59.33/7.99  
% 59.33/7.99  cnf(c_245,plain,
% 59.33/7.99      ( ~ r1_tarski(X0_44,X1_44)
% 59.33/7.99      | r1_tarski(X2_44,X3_44)
% 59.33/7.99      | X2_44 != X0_44
% 59.33/7.99      | X3_44 != X1_44 ),
% 59.33/7.99      theory(equality) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_159494,plain,
% 59.33/7.99      ( r1_tarski(X0_44,X1_44)
% 59.33/7.99      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 59.33/7.99      | X0_44 != u1_struct_0(X0_43)
% 59.33/7.99      | X1_44 != u1_struct_0(X1_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_245]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_159947,plain,
% 59.33/7.99      ( r1_tarski(X0_44,u1_struct_0(X0_43))
% 59.33/7.99      | ~ r1_tarski(u1_struct_0(X1_43),u1_struct_0(X0_43))
% 59.33/7.99      | X0_44 != u1_struct_0(X1_43)
% 59.33/7.99      | u1_struct_0(X0_43) != u1_struct_0(X0_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_159494]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_161476,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 59.33/7.99      | r1_tarski(u1_struct_0(X2_43),u1_struct_0(X1_43))
% 59.33/7.99      | u1_struct_0(X1_43) != u1_struct_0(X1_43)
% 59.33/7.99      | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_159947]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_163578,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 59.33/7.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43)
% 59.33/7.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_161476]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_181302,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(X0_43,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(X0_43,sK1,sK3))
% 59.33/7.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_163578]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_214731,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 59.33/7.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_181302]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_232,plain,( X0_44 = X0_44 ),theory(equality) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_48990,plain,
% 59.33/7.99      ( u1_struct_0(X0_43) = u1_struct_0(X0_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_232]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_150186,plain,
% 59.33/7.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_48990]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_10,plain,
% 59.33/7.99      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 59.33/7.99      | ~ m1_pre_topc(X0,X2)
% 59.33/7.99      | ~ m1_pre_topc(X1,X2)
% 59.33/7.99      | ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ l1_pre_topc(X2)
% 59.33/7.99      | ~ v2_pre_topc(X2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f45]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_220,plain,
% 59.33/7.99      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 59.33/7.99      | ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X0_43,X2_43)
% 59.33/7.99      | ~ m1_pre_topc(X1_43,X2_43)
% 59.33/7.99      | ~ l1_pre_topc(X2_43)
% 59.33/7.99      | ~ v2_pre_topc(X2_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_10]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4683,plain,
% 59.33/7.99      ( r1_tarski(u1_struct_0(X0_43),u1_struct_0(sK2))
% 59.33/7.99      | ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X0_43,sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK2,X1_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | ~ v2_pre_topc(X1_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_220]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_13609,plain,
% 59.33/7.99      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X0_43)
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK2,X0_43)
% 59.33/7.99      | ~ l1_pre_topc(X0_43)
% 59.33/7.99      | ~ v2_pre_topc(X0_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_4683]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_28306,plain,
% 59.33/7.99      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK2,sK2)
% 59.33/7.99      | ~ l1_pre_topc(sK2)
% 59.33/7.99      | ~ v2_pre_topc(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_13609]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_11,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 59.33/7.99      | ~ m1_pre_topc(X0,X2)
% 59.33/7.99      | ~ m1_pre_topc(X1,X2)
% 59.33/7.99      | m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ l1_pre_topc(X2)
% 59.33/7.99      | ~ v2_pre_topc(X2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f44]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_219,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 59.33/7.99      | ~ m1_pre_topc(X0_43,X2_43)
% 59.33/7.99      | ~ m1_pre_topc(X1_43,X2_43)
% 59.33/7.99      | m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ l1_pre_topc(X2_43)
% 59.33/7.99      | ~ v2_pre_topc(X2_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_11]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_15270,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK2,X0_43)
% 59.33/7.99      | ~ l1_pre_topc(X0_43)
% 59.33/7.99      | ~ v2_pre_topc(X0_43) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_219]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_15272,plain,
% 59.33/7.99      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 59.33/7.99      | ~ m1_pre_topc(sK2,sK0)
% 59.33/7.99      | ~ l1_pre_topc(sK0)
% 59.33/7.99      | ~ v2_pre_topc(sK0) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_15270]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_15,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK3,sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f54]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_215,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK3,sK0) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_15]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_664,plain,
% 59.33/7.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_19,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK1,sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f50]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_211,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK1,sK0) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_19]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_668,plain,
% 59.33/7.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 59.33/7.99      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 59.33/7.99      inference(cnf_transformation,[],[f58]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_7,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 59.33/7.99      | ~ l1_pre_topc(X1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f39]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_6,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 59.33/7.99      | ~ l1_pre_topc(X1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f40]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_5,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | ~ l1_pre_topc(X1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f41]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_185,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_4,c_7,c_6,c_5]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_186,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 59.33/7.99      inference(renaming,[status(thm)],[c_185]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_206,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X2_43,X1_43)
% 59.33/7.99      | v2_struct_0(X1_43)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | v2_struct_0(X2_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_186]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_673,plain,
% 59.33/7.99      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 59.33/7.99      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 59.33/7.99      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | v2_struct_0(X1_43) = iProver_top
% 59.33/7.99      | v2_struct_0(X2_43) = iProver_top
% 59.33/7.99      | l1_pre_topc(X0_43) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_3333,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 59.33/7.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | v2_struct_0(sK1) = iProver_top
% 59.33/7.99      | v2_struct_0(sK0) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK0) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_668,c_673]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_23,negated_conjecture,
% 59.33/7.99      ( ~ v2_struct_0(sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f46]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_24,plain,
% 59.33/7.99      ( v2_struct_0(sK0) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_21,negated_conjecture,
% 59.33/7.99      ( l1_pre_topc(sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f48]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_26,plain,
% 59.33/7.99      ( l1_pre_topc(sK0) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_20,negated_conjecture,
% 59.33/7.99      ( ~ v2_struct_0(sK1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f49]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_27,plain,
% 59.33/7.99      ( v2_struct_0(sK1) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_7368,plain,
% 59.33/7.99      ( v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 59.33/7.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_3333,c_24,c_26,c_27]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_7369,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 59.33/7.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top ),
% 59.33/7.99      inference(renaming,[status(thm)],[c_7368]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_7377,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 59.33/7.99      | v2_struct_0(sK3) = iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_664,c_7369]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_13,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK3,sK2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f56]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_217,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK3,sK2) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_13]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_662,plain,
% 59.33/7.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_14,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK1,sK2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f55]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_216,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK1,sK2) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_14]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_663,plain,
% 59.33/7.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_3330,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 59.33/7.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | v2_struct_0(sK2) = iProver_top
% 59.33/7.99      | v2_struct_0(sK1) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK2) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_663,c_673]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_18,negated_conjecture,
% 59.33/7.99      ( ~ v2_struct_0(sK2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f51]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_29,plain,
% 59.33/7.99      ( v2_struct_0(sK2) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f35]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_228,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | l1_pre_topc(X0_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_1]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_17,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK2,sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f52]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_213,negated_conjecture,
% 59.33/7.99      ( m1_pre_topc(sK2,sK0) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_17]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1180,plain,
% 59.33/7.99      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 59.33/7.99      inference(resolution,[status(thm)],[c_228,c_213]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1181,plain,
% 59.33/7.99      ( l1_pre_topc(sK2) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK0) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_6058,plain,
% 59.33/7.99      ( v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 59.33/7.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_3330,c_26,c_27,c_29,c_1181]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_6059,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 59.33/7.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top ),
% 59.33/7.99      inference(renaming,[status(thm)],[c_6058]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_6067,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 59.33/7.99      | v2_struct_0(sK3) = iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_662,c_6059]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_16,negated_conjecture,
% 59.33/7.99      ( ~ v2_struct_0(sK3) ),
% 59.33/7.99      inference(cnf_transformation,[],[f53]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_31,plain,
% 59.33/7.99      ( v2_struct_0(sK3) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_6530,plain,
% 59.33/7.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_6067,c_31]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_7427,plain,
% 59.33/7.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 59.33/7.99      | v2_struct_0(sK3) = iProver_top ),
% 59.33/7.99      inference(demodulation,[status(thm)],[c_7377,c_6530]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_8,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X2,X1)
% 59.33/7.99      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | v2_struct_0(X2)
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | ~ v2_pre_topc(X1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f42]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_222,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X2_43,X1_43)
% 59.33/7.99      | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43))
% 59.33/7.99      | v2_struct_0(X1_43)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | v2_struct_0(X2_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | ~ v2_pre_topc(X1_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_8]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_657,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 59.33/7.99      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43)) = iProver_top
% 59.33/7.99      | v2_struct_0(X1_43) = iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | v2_struct_0(X2_43) = iProver_top
% 59.33/7.99      | l1_pre_topc(X1_43) != iProver_top
% 59.33/7.99      | v2_pre_topc(X1_43) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_666,plain,
% 59.33/7.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_9,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | v2_struct_0(X1)
% 59.33/7.99      | v2_struct_0(X0)
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | ~ v2_pre_topc(X1)
% 59.33/7.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f43]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_221,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | v2_struct_0(X1_43)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | ~ v2_pre_topc(X1_43)
% 59.33/7.99      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_9]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_658,plain,
% 59.33/7.99      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
% 59.33/7.99      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 59.33/7.99      | v2_struct_0(X1_43) = iProver_top
% 59.33/7.99      | v2_struct_0(X0_43) = iProver_top
% 59.33/7.99      | l1_pre_topc(X1_43) != iProver_top
% 59.33/7.99      | v2_pre_topc(X1_43) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1614,plain,
% 59.33/7.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 59.33/7.99      | v2_struct_0(sK2) = iProver_top
% 59.33/7.99      | v2_struct_0(sK0) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK0) != iProver_top
% 59.33/7.99      | v2_pre_topc(sK0) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_666,c_658]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_22,negated_conjecture,
% 59.33/7.99      ( v2_pre_topc(sK0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f47]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1010,plain,
% 59.33/7.99      ( ~ m1_pre_topc(sK2,sK0)
% 59.33/7.99      | v2_struct_0(sK2)
% 59.33/7.99      | v2_struct_0(sK0)
% 59.33/7.99      | ~ l1_pre_topc(sK0)
% 59.33/7.99      | ~ v2_pre_topc(sK0)
% 59.33/7.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_221]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4379,plain,
% 59.33/7.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_1614,c_23,c_22,c_21,c_18,c_17,c_1010]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_2,plain,
% 59.33/7.99      ( m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 59.33/7.99      | ~ l1_pre_topc(X1) ),
% 59.33/7.99      inference(cnf_transformation,[],[f36]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_227,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
% 59.33/7.99      | ~ l1_pre_topc(X1_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_2]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_652,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,X1_43) = iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))) != iProver_top
% 59.33/7.99      | l1_pre_topc(X1_43) != iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4382,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,sK2) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK2) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_4379,c_652]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4387,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,sK2) = iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 59.33/7.99      inference(global_propositional_subsumption,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_4382,c_26,c_1181]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4388,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 59.33/7.99      | m1_pre_topc(X0_43,sK2) = iProver_top ),
% 59.33/7.99      inference(renaming,[status(thm)],[c_4387]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4395,plain,
% 59.33/7.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 59.33/7.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 59.33/7.99      | v2_struct_0(sK2) = iProver_top
% 59.33/7.99      | v2_struct_0(sK0) = iProver_top
% 59.33/7.99      | l1_pre_topc(sK0) != iProver_top
% 59.33/7.99      | v2_pre_topc(sK0) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_657,c_4388]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_4423,plain,
% 59.33/7.99      ( m1_pre_topc(sK2,sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK2,sK0)
% 59.33/7.99      | v2_struct_0(sK2)
% 59.33/7.99      | v2_struct_0(sK0)
% 59.33/7.99      | ~ l1_pre_topc(sK0)
% 59.33/7.99      | ~ v2_pre_topc(sK0) ),
% 59.33/7.99      inference(predicate_to_equality_rev,[status(thm)],[c_4395]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_225,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ m1_pre_topc(X2_43,X1_43)
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 59.33/7.99      | v2_struct_0(X1_43)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | v2_struct_0(X2_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_5]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1051,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,sK0)
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK3),sK0)
% 59.33/7.99      | ~ m1_pre_topc(sK3,sK0)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | v2_struct_0(sK3)
% 59.33/7.99      | v2_struct_0(sK0)
% 59.33/7.99      | ~ l1_pre_topc(sK0) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_225]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1379,plain,
% 59.33/7.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 59.33/7.99      | ~ m1_pre_topc(sK3,sK0)
% 59.33/7.99      | ~ m1_pre_topc(sK1,sK0)
% 59.33/7.99      | v2_struct_0(sK3)
% 59.33/7.99      | v2_struct_0(sK1)
% 59.33/7.99      | v2_struct_0(sK0)
% 59.33/7.99      | ~ l1_pre_topc(sK0) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_1051]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1041,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,sK2)
% 59.33/7.99      | m1_pre_topc(k1_tsep_1(sK2,X0_43,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK3,sK2)
% 59.33/7.99      | v2_struct_0(X0_43)
% 59.33/7.99      | v2_struct_0(sK2)
% 59.33/7.99      | v2_struct_0(sK3)
% 59.33/7.99      | ~ l1_pre_topc(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_225]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1364,plain,
% 59.33/7.99      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK3,sK2)
% 59.33/7.99      | ~ m1_pre_topc(sK1,sK2)
% 59.33/7.99      | v2_struct_0(sK2)
% 59.33/7.99      | v2_struct_0(sK3)
% 59.33/7.99      | v2_struct_0(sK1)
% 59.33/7.99      | ~ l1_pre_topc(sK2) ),
% 59.33/7.99      inference(instantiation,[status(thm)],[c_1041]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_0,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0,X1)
% 59.33/7.99      | ~ l1_pre_topc(X1)
% 59.33/7.99      | ~ v2_pre_topc(X1)
% 59.33/7.99      | v2_pre_topc(X0) ),
% 59.33/7.99      inference(cnf_transformation,[],[f34]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_229,plain,
% 59.33/7.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 59.33/7.99      | ~ l1_pre_topc(X1_43)
% 59.33/7.99      | ~ v2_pre_topc(X1_43)
% 59.33/7.99      | v2_pre_topc(X0_43) ),
% 59.33/7.99      inference(subtyping,[status(esa)],[c_0]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_650,plain,
% 59.33/7.99      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 59.33/7.99      | l1_pre_topc(X1_43) != iProver_top
% 59.33/7.99      | v2_pre_topc(X1_43) != iProver_top
% 59.33/7.99      | v2_pre_topc(X0_43) = iProver_top ),
% 59.33/7.99      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1236,plain,
% 59.33/7.99      ( l1_pre_topc(sK0) != iProver_top
% 59.33/7.99      | v2_pre_topc(sK2) = iProver_top
% 59.33/7.99      | v2_pre_topc(sK0) != iProver_top ),
% 59.33/7.99      inference(superposition,[status(thm)],[c_666,c_650]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_1248,plain,
% 59.33/7.99      ( ~ l1_pre_topc(sK0) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK0) ),
% 59.33/7.99      inference(predicate_to_equality_rev,[status(thm)],[c_1236]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(c_12,negated_conjecture,
% 59.33/7.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 59.33/7.99      inference(cnf_transformation,[],[f57]) ).
% 59.33/7.99  
% 59.33/7.99  cnf(contradiction,plain,
% 59.33/7.99      ( $false ),
% 59.33/7.99      inference(minisat,
% 59.33/7.99                [status(thm)],
% 59.33/7.99                [c_214731,c_150186,c_28306,c_15272,c_7427,c_4423,c_1379,
% 59.33/7.99                 c_1364,c_1248,c_1180,c_12,c_13,c_14,c_15,c_31,c_16,c_17,
% 59.33/7.99                 c_18,c_19,c_20,c_21,c_22,c_23]) ).
% 59.33/7.99  
% 59.33/7.99  
% 59.33/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.33/7.99  
% 59.33/7.99  ------                               Statistics
% 59.33/7.99  
% 59.33/7.99  ------ Selected
% 59.33/7.99  
% 59.33/7.99  total_time:                             7.244
% 59.33/7.99  
%------------------------------------------------------------------------------
