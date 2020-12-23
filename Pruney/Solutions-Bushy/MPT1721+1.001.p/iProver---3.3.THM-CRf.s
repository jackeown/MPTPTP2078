%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1721+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  147 (1088 expanded)
%              Number of clauses        :   99 ( 257 expanded)
%              Number of leaves         :   11 ( 382 expanded)
%              Depth                    :   25
%              Number of atoms          :  703 (11589 expanded)
%              Number of equality atoms :  119 ( 218 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f26,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25,f24,f23,f22])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
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
    inference(equality_resolution,[],[f27])).

fof(f48,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_227,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_228,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_230,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_20])).

cnf(c_231,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_2257,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_7652,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_281,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | u1_struct_0(k2_tsep_1(X1,X2,X0)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_282,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_286,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_19,c_17])).

cnf(c_473,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,sK2),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(X0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_20])).

cnf(c_474,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_476,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_22,c_18,c_16])).

cnf(c_477,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_1230,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_520,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_521,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_525,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_22])).

cnf(c_526,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_1414,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,sK2))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_1566,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_545,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_546,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_22])).

cnf(c_551,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_1429,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v1_pre_topc(k2_tsep_1(sK0,X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_1606,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_570,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_571,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_22])).

cnf(c_576,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_575])).

cnf(c_1444,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_1642,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_2641,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_19,c_18,c_17,c_16,c_477,c_1566,c_1606,c_1642])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1243,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2648,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_xboole_0(u1_struct_0(sK1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1243])).

cnf(c_2654,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2648])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1240,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_247,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_248,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_252,plain,
    ( ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_20])).

cnf(c_253,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_1231,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1244,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2766,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X2)) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1244])).

cnf(c_3265,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_2766])).

cnf(c_3311,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_3265])).

cnf(c_27,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_31,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_32,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1394,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1395,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1404,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1755,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1756,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_1510,plain,
    ( r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2661,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_2662,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_3604,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3311,c_27,c_31,c_32,c_1395,c_1756,c_2662])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1241,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3310,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_3265])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1399,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1727,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1728,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1727])).

cnf(c_2627,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_2628,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_3560,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3310,c_29,c_31,c_33,c_1395,c_1728,c_2628])).

cnf(c_3571,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_2766])).

cnf(c_6245,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_3571])).

cnf(c_6316,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6245,c_29,c_31,c_33,c_1728])).

cnf(c_6321,plain,
    ( r1_tarski(X0,u1_struct_0(sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6316,c_1244])).

cnf(c_6481,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3604,c_6321])).

cnf(c_6929,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6481,c_27,c_31,c_32,c_1756])).

cnf(c_6934,plain,
    ( r1_tarski(X0,u1_struct_0(sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6929,c_1244])).

cnf(c_7546,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_6934])).

cnf(c_7617,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7546])).

cnf(c_10,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7652,c_7617,c_1642,c_10,c_14,c_16,c_17,c_18,c_19])).


%------------------------------------------------------------------------------
