%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:10 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 730 expanded)
%              Number of clauses        :  101 ( 191 expanded)
%              Number of leaves         :   13 ( 247 expanded)
%              Depth                    :   23
%              Number of atoms          :  798 (7611 expanded)
%              Number of equality atoms :  242 ( 341 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3)
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK3)
        & m1_pre_topc(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3)
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3)
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(sK1,X3)
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
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
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

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
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
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
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
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
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
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
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
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_226,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ m1_pre_topc(X2_45,X1_45)
    | m1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45),X1_45)
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | v2_struct_0(X2_45)
    | ~ l1_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_684,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_pre_topc(X2_45,X1_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45),X1_45) = iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_213,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_697,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_211,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_699,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_4,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X2)
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_227,plain,
    ( r1_tsep_1(X0_45,X1_45)
    | ~ m1_pre_topc(X0_45,X2_45)
    | ~ m1_pre_topc(X1_45,X2_45)
    | ~ m1_pre_topc(k2_tsep_1(X2_45,X0_45,X1_45),X2_45)
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | v2_struct_0(X2_45)
    | v2_struct_0(k2_tsep_1(X2_45,X0_45,X1_45))
    | ~ v1_pre_topc(k2_tsep_1(X2_45,X0_45,X1_45))
    | ~ l1_pre_topc(X2_45)
    | u1_struct_0(k2_tsep_1(X2_45,X0_45,X1_45)) = k3_xboole_0(u1_struct_0(X0_45),u1_struct_0(X1_45)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_683,plain,
    ( u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = k3_xboole_0(u1_struct_0(X1_45),u1_struct_0(X2_45))
    | r1_tsep_1(X1_45,X2_45) = iProver_top
    | m1_pre_topc(X1_45,X0_45) != iProver_top
    | m1_pre_topc(X2_45,X0_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45),X0_45) != iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45)) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_225,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ m1_pre_topc(X2_45,X1_45)
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | v2_struct_0(X2_45)
    | v1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45))
    | ~ l1_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_685,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_pre_topc(X2_45,X1_45) != iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | v1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45)) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ m1_pre_topc(X2_45,X1_45)
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | v2_struct_0(X2_45)
    | ~ v2_struct_0(k2_tsep_1(X1_45,X0_45,X2_45))
    | ~ l1_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_686,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_pre_topc(X2_45,X1_45) != iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | v2_struct_0(k2_tsep_1(X1_45,X0_45,X2_45)) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_879,plain,
    ( u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = k3_xboole_0(u1_struct_0(X1_45),u1_struct_0(X2_45))
    | r1_tsep_1(X1_45,X2_45) = iProver_top
    | m1_pre_topc(X1_45,X0_45) != iProver_top
    | m1_pre_topc(X2_45,X0_45) != iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_683,c_685,c_686,c_684])).

cnf(c_4335,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45))
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK0) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_879])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5714,plain,
    ( v2_struct_0(X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK0) != iProver_top
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4335,c_25,c_27,c_28])).

cnf(c_5715,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45))
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK0) != iProver_top
    | v2_struct_0(X0_45) = iProver_top ),
    inference(renaming,[status(thm)],[c_5714])).

cnf(c_5725,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_5715])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_217,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_693,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_216,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_694,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_4332,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45))
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_879])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_230,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ l1_pre_topc(X1_45)
    | l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_215,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1167,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_230,c_215])).

cnf(c_1168,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_4791,plain,
    ( v2_struct_0(X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4332,c_27,c_28,c_32,c_1168])).

cnf(c_4792,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45))
    | r1_tsep_1(sK1,X0_45) = iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | v2_struct_0(X0_45) = iProver_top ),
    inference(renaming,[status(thm)],[c_4791])).

cnf(c_4801,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_4792])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4944,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4801,c_30,c_36])).

cnf(c_5755,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5725,c_4944])).

cnf(c_6164,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5755,c_30,c_36])).

cnf(c_10,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_221,plain,
    ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45))
    | ~ m1_pre_topc(X0_45,X2_45)
    | ~ m1_pre_topc(X1_45,X2_45)
    | ~ m1_pre_topc(X0_45,X1_45)
    | ~ l1_pre_topc(X2_45)
    | ~ v2_pre_topc(X2_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_689,plain,
    ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45)) = iProver_top
    | m1_pre_topc(X0_45,X2_45) != iProver_top
    | m1_pre_topc(X1_45,X2_45) != iProver_top
    | m1_pre_topc(X0_45,X1_45) != iProver_top
    | l1_pre_topc(X2_45) != iProver_top
    | v2_pre_topc(X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_3559,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)),u1_struct_0(X3_45)) = iProver_top
    | m1_pre_topc(X1_45,X0_45) != iProver_top
    | m1_pre_topc(X2_45,X0_45) != iProver_top
    | m1_pre_topc(X3_45,X0_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45),X3_45) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v2_pre_topc(X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_689])).

cnf(c_6575,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_3559])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_695,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_231,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ l1_pre_topc(X1_45)
    | ~ v2_pre_topc(X1_45)
    | v2_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_679,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v2_pre_topc(X1_45) != iProver_top
    | v2_pre_topc(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_1228,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_679])).

cnf(c_30317,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6575,c_26,c_27,c_28,c_30,c_32,c_34,c_35,c_1168,c_1228])).

cnf(c_30318,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_30317])).

cnf(c_11,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_220,plain,
    ( ~ r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45))
    | ~ m1_pre_topc(X0_45,X2_45)
    | ~ m1_pre_topc(X1_45,X2_45)
    | m1_pre_topc(X0_45,X1_45)
    | ~ l1_pre_topc(X2_45)
    | ~ v2_pre_topc(X2_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_690,plain,
    ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45)) != iProver_top
    | m1_pre_topc(X0_45,X2_45) != iProver_top
    | m1_pre_topc(X1_45,X2_45) != iProver_top
    | m1_pre_topc(X0_45,X1_45) = iProver_top
    | l1_pre_topc(X2_45) != iProver_top
    | v2_pre_topc(X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_30327,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_pre_topc(X0_45,sK3) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_45) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v2_pre_topc(X1_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_30318,c_690])).

cnf(c_30538,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_45) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
    | m1_pre_topc(sK3,X0_45) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_30327])).

cnf(c_30608,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30538])).

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

cnf(c_223,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ m1_pre_topc(X2_45,X1_45)
    | m1_pre_topc(X0_45,k1_tsep_1(X1_45,X0_45,X2_45))
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | v2_struct_0(X2_45)
    | ~ l1_pre_topc(X1_45)
    | ~ v2_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_687,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_pre_topc(X2_45,X1_45) != iProver_top
    | m1_pre_topc(X0_45,k1_tsep_1(X1_45,X0_45,X2_45)) = iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(X2_45) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v2_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_222,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | v2_struct_0(X1_45)
    | v2_struct_0(X0_45)
    | ~ l1_pre_topc(X1_45)
    | ~ v2_pre_topc(X1_45)
    | g1_pre_topc(u1_struct_0(X0_45),u1_pre_topc(X0_45)) = k1_tsep_1(X1_45,X0_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_688,plain,
    ( g1_pre_topc(u1_struct_0(X0_45),u1_pre_topc(X0_45)) = k1_tsep_1(X1_45,X0_45,X0_45)
    | m1_pre_topc(X0_45,X1_45) != iProver_top
    | v2_struct_0(X1_45) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v2_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_2782,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3)
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_688])).

cnf(c_1047,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_3980,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2782,c_24,c_23,c_22,c_17,c_16,c_1047])).

cnf(c_2,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_229,plain,
    ( m1_pre_topc(X0_45,X1_45)
    | ~ m1_pre_topc(X0_45,g1_pre_topc(u1_struct_0(X1_45),u1_pre_topc(X1_45)))
    | ~ l1_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_681,plain,
    ( m1_pre_topc(X0_45,X1_45) = iProver_top
    | m1_pre_topc(X0_45,g1_pre_topc(u1_struct_0(X1_45),u1_pre_topc(X1_45))) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_3983,plain,
    ( m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | m1_pre_topc(X0_45,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_681])).

cnf(c_4573,plain,
    ( m1_pre_topc(X0_45,sK3) = iProver_top
    | m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3983,c_27,c_1168])).

cnf(c_4574,plain,
    ( m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | m1_pre_topc(X0_45,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4573])).

cnf(c_4581,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_4574])).

cnf(c_1096,plain,
    ( ~ m1_pre_topc(X0_45,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_45,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_45)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_1483,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_1484,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_33,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_31,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30608,c_4581,c_1484,c_1168,c_37,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:37:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 8.04/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.49  
% 8.04/1.49  ------  iProver source info
% 8.04/1.49  
% 8.04/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.49  git: non_committed_changes: false
% 8.04/1.49  git: last_make_outside_of_git: false
% 8.04/1.49  
% 8.04/1.49  ------ 
% 8.04/1.49  ------ Parsing...
% 8.04/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.49  ------ Proving...
% 8.04/1.49  ------ Problem Properties 
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  clauses                                 25
% 8.04/1.49  conjectures                             13
% 8.04/1.49  EPR                                     14
% 8.04/1.49  Horn                                    18
% 8.04/1.49  unary                                   13
% 8.04/1.49  binary                                  0
% 8.04/1.49  lits                                    93
% 8.04/1.49  lits eq                                 4
% 8.04/1.49  fd_pure                                 0
% 8.04/1.49  fd_pseudo                               0
% 8.04/1.49  fd_cond                                 0
% 8.04/1.49  fd_pseudo_cond                          1
% 8.04/1.49  AC symbols                              0
% 8.04/1.49  
% 8.04/1.49  ------ Input Options Time Limit: Unbounded
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  ------ 
% 8.04/1.49  Current options:
% 8.04/1.49  ------ 
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  ------ Proving...
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  % SZS status Theorem for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  fof(f5,axiom,(
% 8.04/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f17,plain,(
% 8.04/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f5])).
% 8.04/1.49  
% 8.04/1.49  fof(f18,plain,(
% 8.04/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.04/1.49    inference(flattening,[],[f17])).
% 8.04/1.49  
% 8.04/1.49  fof(f41,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f18])).
% 8.04/1.49  
% 8.04/1.49  fof(f9,conjecture,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f10,negated_conjecture,(
% 8.04/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 8.04/1.49    inference(negated_conjecture,[],[f9])).
% 8.04/1.49  
% 8.04/1.49  fof(f25,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f10])).
% 8.04/1.49  
% 8.04/1.49  fof(f26,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.04/1.49    inference(flattening,[],[f25])).
% 8.04/1.49  
% 8.04/1.49  fof(f32,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK3) & m1_pre_topc(X1,sK3) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f31,plain,(
% 8.04/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f30,plain,(
% 8.04/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f29,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f33,plain,(
% 8.04/1.49    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 8.04/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f32,f31,f30,f29])).
% 8.04/1.49  
% 8.04/1.49  fof(f52,plain,(
% 8.04/1.49    m1_pre_topc(sK2,sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f50,plain,(
% 8.04/1.49    m1_pre_topc(sK1,sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f4,axiom,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f15,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f4])).
% 8.04/1.49  
% 8.04/1.49  fof(f16,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.04/1.49    inference(flattening,[],[f15])).
% 8.04/1.49  
% 8.04/1.49  fof(f27,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.04/1.49    inference(nnf_transformation,[],[f16])).
% 8.04/1.49  
% 8.04/1.49  fof(f37,plain,(
% 8.04/1.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f27])).
% 8.04/1.49  
% 8.04/1.49  fof(f59,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(equality_resolution,[],[f37])).
% 8.04/1.49  
% 8.04/1.49  fof(f40,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f18])).
% 8.04/1.49  
% 8.04/1.49  fof(f39,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f18])).
% 8.04/1.49  
% 8.04/1.49  fof(f46,plain,(
% 8.04/1.49    ~v2_struct_0(sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f48,plain,(
% 8.04/1.49    l1_pre_topc(sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f49,plain,(
% 8.04/1.49    ~v2_struct_0(sK1)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f56,plain,(
% 8.04/1.49    m1_pre_topc(sK2,sK3)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f55,plain,(
% 8.04/1.49    m1_pre_topc(sK1,sK3)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f53,plain,(
% 8.04/1.49    ~v2_struct_0(sK3)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f2,axiom,(
% 8.04/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f13,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.04/1.49    inference(ennf_transformation,[],[f2])).
% 8.04/1.49  
% 8.04/1.49  fof(f35,plain,(
% 8.04/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f13])).
% 8.04/1.49  
% 8.04/1.49  fof(f54,plain,(
% 8.04/1.49    m1_pre_topc(sK3,sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f51,plain,(
% 8.04/1.49    ~v2_struct_0(sK2)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f57,plain,(
% 8.04/1.49    ~r1_tsep_1(sK1,sK2)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f8,axiom,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f23,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f8])).
% 8.04/1.49  
% 8.04/1.49  fof(f24,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.04/1.49    inference(flattening,[],[f23])).
% 8.04/1.49  
% 8.04/1.49  fof(f28,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.04/1.49    inference(nnf_transformation,[],[f24])).
% 8.04/1.49  
% 8.04/1.49  fof(f45,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f47,plain,(
% 8.04/1.49    v2_pre_topc(sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  fof(f1,axiom,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f11,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f1])).
% 8.04/1.49  
% 8.04/1.49  fof(f12,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.04/1.49    inference(flattening,[],[f11])).
% 8.04/1.49  
% 8.04/1.49  fof(f34,plain,(
% 8.04/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f12])).
% 8.04/1.49  
% 8.04/1.49  fof(f44,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f6,axiom,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f19,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f6])).
% 8.04/1.49  
% 8.04/1.49  fof(f20,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.04/1.49    inference(flattening,[],[f19])).
% 8.04/1.49  
% 8.04/1.49  fof(f42,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f20])).
% 8.04/1.49  
% 8.04/1.49  fof(f7,axiom,(
% 8.04/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f21,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f7])).
% 8.04/1.49  
% 8.04/1.49  fof(f22,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.04/1.49    inference(flattening,[],[f21])).
% 8.04/1.49  
% 8.04/1.49  fof(f43,plain,(
% 8.04/1.49    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f22])).
% 8.04/1.49  
% 8.04/1.49  fof(f3,axiom,(
% 8.04/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f14,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 8.04/1.49    inference(ennf_transformation,[],[f3])).
% 8.04/1.49  
% 8.04/1.49  fof(f36,plain,(
% 8.04/1.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f14])).
% 8.04/1.49  
% 8.04/1.49  fof(f58,plain,(
% 8.04/1.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 8.04/1.49    inference(cnf_transformation,[],[f33])).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X2,X1)
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | v2_struct_0(X2)
% 8.04/1.49      | ~ l1_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f41]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_226,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X2_45,X1_45)
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45),X1_45)
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(X2_45)
% 8.04/1.49      | ~ l1_pre_topc(X1_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_684,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45),X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_18,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK2,sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_213,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK2,sK0) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_697,plain,
% 8.04/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_20,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK1,sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_211,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK1,sK0) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_699,plain,
% 8.04/1.49      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4,plain,
% 8.04/1.49      ( r1_tsep_1(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X0,X2)
% 8.04/1.49      | ~ m1_pre_topc(X1,X2)
% 8.04/1.49      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 8.04/1.49      | v2_struct_0(X2)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 8.04/1.49      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 8.04/1.49      | ~ l1_pre_topc(X2)
% 8.04/1.49      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_227,plain,
% 8.04/1.49      ( r1_tsep_1(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X0_45,X2_45)
% 8.04/1.49      | ~ m1_pre_topc(X1_45,X2_45)
% 8.04/1.49      | ~ m1_pre_topc(k2_tsep_1(X2_45,X0_45,X1_45),X2_45)
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(X2_45)
% 8.04/1.49      | v2_struct_0(k2_tsep_1(X2_45,X0_45,X1_45))
% 8.04/1.49      | ~ v1_pre_topc(k2_tsep_1(X2_45,X0_45,X1_45))
% 8.04/1.49      | ~ l1_pre_topc(X2_45)
% 8.04/1.49      | u1_struct_0(k2_tsep_1(X2_45,X0_45,X1_45)) = k3_xboole_0(u1_struct_0(X0_45),u1_struct_0(X1_45)) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_683,plain,
% 8.04/1.49      ( u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = k3_xboole_0(u1_struct_0(X1_45),u1_struct_0(X2_45))
% 8.04/1.49      | r1_tsep_1(X1_45,X2_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X1_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45),X0_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = iProver_top
% 8.04/1.49      | v1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45)) != iProver_top
% 8.04/1.49      | l1_pre_topc(X0_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_6,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X2,X1)
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | v2_struct_0(X2)
% 8.04/1.49      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 8.04/1.49      | ~ l1_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_225,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X2_45,X1_45)
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(X2_45)
% 8.04/1.49      | v1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45))
% 8.04/1.49      | ~ l1_pre_topc(X1_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_685,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X1_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | v1_pre_topc(k2_tsep_1(X1_45,X0_45,X2_45)) = iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X2,X1)
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | v2_struct_0(X2)
% 8.04/1.49      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 8.04/1.49      | ~ l1_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_224,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X2_45,X1_45)
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(X2_45)
% 8.04/1.49      | ~ v2_struct_0(k2_tsep_1(X1_45,X0_45,X2_45))
% 8.04/1.49      | ~ l1_pre_topc(X1_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_686,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X1_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | v2_struct_0(k2_tsep_1(X1_45,X0_45,X2_45)) != iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_879,plain,
% 8.04/1.49      ( u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)) = k3_xboole_0(u1_struct_0(X1_45),u1_struct_0(X2_45))
% 8.04/1.49      | r1_tsep_1(X1_45,X2_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X1_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X0_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X0_45) != iProver_top ),
% 8.04/1.49      inference(forward_subsumption_resolution,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_683,c_685,c_686,c_684]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4335,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45))
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK0) != iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | v2_struct_0(sK0) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_699,c_879]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_24,negated_conjecture,
% 8.04/1.49      ( ~ v2_struct_0(sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_25,plain,
% 8.04/1.49      ( v2_struct_0(sK0) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_22,negated_conjecture,
% 8.04/1.49      ( l1_pre_topc(sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_27,plain,
% 8.04/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_21,negated_conjecture,
% 8.04/1.49      ( ~ v2_struct_0(sK1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_28,plain,
% 8.04/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5714,plain,
% 8.04/1.49      ( v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK0) != iProver_top
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45)) ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_4335,c_25,c_27,c_28]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5715,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK0,sK1,X0_45))
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK0) != iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top ),
% 8.04/1.49      inference(renaming,[status(thm)],[c_5714]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5725,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 8.04/1.49      | r1_tsep_1(sK1,sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_697,c_5715]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_14,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK2,sK3) ),
% 8.04/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_217,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK2,sK3) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_693,plain,
% 8.04/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK1,sK3) ),
% 8.04/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_216,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK1,sK3) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_694,plain,
% 8.04/1.49      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4332,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45))
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_694,c_879]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17,negated_conjecture,
% 8.04/1.49      ( ~ v2_struct_0(sK3) ),
% 8.04/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_32,plain,
% 8.04/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f35]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_230,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ l1_pre_topc(X1_45)
% 8.04/1.49      | l1_pre_topc(X0_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_16,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK3,sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_215,negated_conjecture,
% 8.04/1.49      ( m1_pre_topc(sK3,sK0) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1167,plain,
% 8.04/1.49      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 8.04/1.49      inference(resolution,[status(thm)],[c_230,c_215]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1168,plain,
% 8.04/1.49      ( l1_pre_topc(sK3) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4791,plain,
% 8.04/1.49      ( v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45)) ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_4332,c_27,c_28,c_32,c_1168]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4792,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_45)) = u1_struct_0(k2_tsep_1(sK3,sK1,X0_45))
% 8.04/1.49      | r1_tsep_1(sK1,X0_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top ),
% 8.04/1.49      inference(renaming,[status(thm)],[c_4791]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4801,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
% 8.04/1.49      | r1_tsep_1(sK1,sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_693,c_4792]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_19,negated_conjecture,
% 8.04/1.49      ( ~ v2_struct_0(sK2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30,plain,
% 8.04/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13,negated_conjecture,
% 8.04/1.49      ( ~ r1_tsep_1(sK1,sK2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_36,plain,
% 8.04/1.49      ( r1_tsep_1(sK1,sK2) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4944,plain,
% 8.04/1.49      ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_4801,c_30,c_36]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5755,plain,
% 8.04/1.49      ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 8.04/1.49      | r1_tsep_1(sK1,sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_5725,c_4944]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_6164,plain,
% 8.04/1.49      ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_5755,c_30,c_36]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 8.04/1.49      | ~ m1_pre_topc(X0,X2)
% 8.04/1.49      | ~ m1_pre_topc(X1,X2)
% 8.04/1.49      | ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ l1_pre_topc(X2)
% 8.04/1.49      | ~ v2_pre_topc(X2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_221,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45))
% 8.04/1.49      | ~ m1_pre_topc(X0_45,X2_45)
% 8.04/1.49      | ~ m1_pre_topc(X1_45,X2_45)
% 8.04/1.49      | ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ l1_pre_topc(X2_45)
% 8.04/1.49      | ~ v2_pre_topc(X2_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_689,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45)) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,X2_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X1_45,X2_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | l1_pre_topc(X2_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X2_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3559,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(k2_tsep_1(X0_45,X1_45,X2_45)),u1_struct_0(X3_45)) = iProver_top
% 8.04/1.49      | m1_pre_topc(X1_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X3_45,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(X0_45,X1_45,X2_45),X3_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X0_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X0_45) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_684,c_689]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_6575,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK1,sK3) != iProver_top
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.04/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6164,c_3559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_23,negated_conjecture,
% 8.04/1.49      ( v2_pre_topc(sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_26,plain,
% 8.04/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_34,plain,
% 8.04/1.49      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_35,plain,
% 8.04/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_695,plain,
% 8.04/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_0,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ l1_pre_topc(X1)
% 8.04/1.49      | ~ v2_pre_topc(X1)
% 8.04/1.49      | v2_pre_topc(X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_231,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ l1_pre_topc(X1_45)
% 8.04/1.49      | ~ v2_pre_topc(X1_45)
% 8.04/1.49      | v2_pre_topc(X0_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_679,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X1_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X0_45) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1228,plain,
% 8.04/1.49      ( l1_pre_topc(sK0) != iProver_top
% 8.04/1.49      | v2_pre_topc(sK3) = iProver_top
% 8.04/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_695,c_679]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30317,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_6575,c_26,c_27,c_28,c_30,c_32,c_34,c_35,c_1168,c_1228]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30318,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_45)) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top ),
% 8.04/1.49      inference(renaming,[status(thm)],[c_30317]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11,plain,
% 8.04/1.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 8.04/1.49      | ~ m1_pre_topc(X0,X2)
% 8.04/1.49      | ~ m1_pre_topc(X1,X2)
% 8.04/1.49      | m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ l1_pre_topc(X2)
% 8.04/1.49      | ~ v2_pre_topc(X2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_220,plain,
% 8.04/1.49      ( ~ r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45))
% 8.04/1.49      | ~ m1_pre_topc(X0_45,X2_45)
% 8.04/1.49      | ~ m1_pre_topc(X1_45,X2_45)
% 8.04/1.49      | m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ l1_pre_topc(X2_45)
% 8.04/1.49      | ~ v2_pre_topc(X2_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_690,plain,
% 8.04/1.49      ( r1_tarski(u1_struct_0(X0_45),u1_struct_0(X1_45)) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,X2_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X1_45,X2_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,X1_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X2_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X2_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30327,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_30318,c_690]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30538,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
% 8.04/1.49      | m1_pre_topc(sK3,X0_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK3,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK1,sK3) != iProver_top
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | l1_pre_topc(X0_45) != iProver_top
% 8.04/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.04/1.49      | v2_pre_topc(X0_45) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_684,c_30327]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30608,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK3,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK1,sK3) != iProver_top
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top
% 8.04/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_30538]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X2,X1)
% 8.04/1.49      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | v2_struct_0(X2)
% 8.04/1.49      | ~ l1_pre_topc(X1)
% 8.04/1.49      | ~ v2_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_223,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X2_45,X1_45)
% 8.04/1.49      | m1_pre_topc(X0_45,k1_tsep_1(X1_45,X0_45,X2_45))
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(X2_45)
% 8.04/1.49      | ~ l1_pre_topc(X1_45)
% 8.04/1.49      | ~ v2_pre_topc(X1_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_687,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X2_45,X1_45) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,k1_tsep_1(X1_45,X0_45,X2_45)) = iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X2_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.04/1.49      | v2_struct_0(X1)
% 8.04/1.49      | v2_struct_0(X0)
% 8.04/1.49      | ~ l1_pre_topc(X1)
% 8.04/1.49      | ~ v2_pre_topc(X1)
% 8.04/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_222,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | v2_struct_0(X1_45)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | ~ l1_pre_topc(X1_45)
% 8.04/1.49      | ~ v2_pre_topc(X1_45)
% 8.04/1.49      | g1_pre_topc(u1_struct_0(X0_45),u1_pre_topc(X0_45)) = k1_tsep_1(X1_45,X0_45,X0_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_688,plain,
% 8.04/1.49      ( g1_pre_topc(u1_struct_0(X0_45),u1_pre_topc(X0_45)) = k1_tsep_1(X1_45,X0_45,X0_45)
% 8.04/1.49      | m1_pre_topc(X0_45,X1_45) != iProver_top
% 8.04/1.49      | v2_struct_0(X1_45) = iProver_top
% 8.04/1.49      | v2_struct_0(X0_45) = iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top
% 8.04/1.49      | v2_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2782,plain,
% 8.04/1.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3)
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK0) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top
% 8.04/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_695,c_688]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1047,plain,
% 8.04/1.49      ( ~ m1_pre_topc(sK3,sK0)
% 8.04/1.49      | v2_struct_0(sK3)
% 8.04/1.49      | v2_struct_0(sK0)
% 8.04/1.49      | ~ l1_pre_topc(sK0)
% 8.04/1.49      | ~ v2_pre_topc(sK0)
% 8.04/1.49      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_222]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3980,plain,
% 8.04/1.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_2782,c_24,c_23,c_22,c_17,c_16,c_1047]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2,plain,
% 8.04/1.49      ( m1_pre_topc(X0,X1)
% 8.04/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 8.04/1.49      | ~ l1_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_229,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45)
% 8.04/1.49      | ~ m1_pre_topc(X0_45,g1_pre_topc(u1_struct_0(X1_45),u1_pre_topc(X1_45)))
% 8.04/1.49      | ~ l1_pre_topc(X1_45) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_681,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,X1_45) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,g1_pre_topc(u1_struct_0(X1_45),u1_pre_topc(X1_45))) != iProver_top
% 8.04/1.49      | l1_pre_topc(X1_45) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3983,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3980,c_681]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4573,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,sK3) = iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_3983,c_27,c_1168]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4574,plain,
% 8.04/1.49      ( m1_pre_topc(X0_45,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 8.04/1.49      | m1_pre_topc(X0_45,sK3) = iProver_top ),
% 8.04/1.49      inference(renaming,[status(thm)],[c_4573]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4581,plain,
% 8.04/1.49      ( m1_pre_topc(sK3,sK3) = iProver_top
% 8.04/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.04/1.49      | v2_struct_0(sK3) = iProver_top
% 8.04/1.49      | v2_struct_0(sK0) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top
% 8.04/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_687,c_4574]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1096,plain,
% 8.04/1.49      ( ~ m1_pre_topc(X0_45,sK0)
% 8.04/1.49      | m1_pre_topc(k2_tsep_1(sK0,X0_45,sK2),sK0)
% 8.04/1.49      | ~ m1_pre_topc(sK2,sK0)
% 8.04/1.49      | v2_struct_0(X0_45)
% 8.04/1.49      | v2_struct_0(sK2)
% 8.04/1.49      | v2_struct_0(sK0)
% 8.04/1.49      | ~ l1_pre_topc(sK0) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_226]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1483,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 8.04/1.49      | ~ m1_pre_topc(sK2,sK0)
% 8.04/1.49      | ~ m1_pre_topc(sK1,sK0)
% 8.04/1.49      | v2_struct_0(sK2)
% 8.04/1.49      | v2_struct_0(sK1)
% 8.04/1.49      | v2_struct_0(sK0)
% 8.04/1.49      | ~ l1_pre_topc(sK0) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_1096]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1484,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 8.04/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.04/1.49      | m1_pre_topc(sK1,sK0) != iProver_top
% 8.04/1.49      | v2_struct_0(sK2) = iProver_top
% 8.04/1.49      | v2_struct_0(sK1) = iProver_top
% 8.04/1.49      | v2_struct_0(sK0) = iProver_top
% 8.04/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12,negated_conjecture,
% 8.04/1.49      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
% 8.04/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_37,plain,
% 8.04/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_33,plain,
% 8.04/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31,plain,
% 8.04/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_29,plain,
% 8.04/1.49      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(contradiction,plain,
% 8.04/1.49      ( $false ),
% 8.04/1.49      inference(minisat,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_30608,c_4581,c_1484,c_1168,c_37,c_35,c_34,c_33,c_32,
% 8.04/1.49                 c_31,c_30,c_29,c_28,c_27,c_26,c_25]) ).
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  ------                               Statistics
% 8.04/1.49  
% 8.04/1.49  ------ Selected
% 8.04/1.49  
% 8.04/1.49  total_time:                             0.996
% 8.04/1.49  
%------------------------------------------------------------------------------
