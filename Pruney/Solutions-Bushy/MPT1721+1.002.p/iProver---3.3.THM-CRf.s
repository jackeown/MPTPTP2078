%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1721+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 780 expanded)
%              Number of clauses        :   82 ( 176 expanded)
%              Number of leaves         :   12 ( 270 expanded)
%              Depth                    :   18
%              Number of atoms          :  630 (8395 expanded)
%              Number of equality atoms :  168 ( 340 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27,f26,f25,f24])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
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
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
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
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_606,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_608,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_623,plain,
    ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | r1_tsep_1(X1,X2) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,X1,X2)) = iProver_top
    | v1_pre_topc(k2_tsep_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_621,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_620,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X1,X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_622,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_770,plain,
    ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | r1_tsep_1(X1,X2) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_621,c_620,c_622])).

cnf(c_5807,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_770])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7970,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | r1_tsep_1(X0,sK2) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5807,c_25,c_27,c_30])).

cnf(c_7971,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7970])).

cnf(c_7983,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_7971])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_611,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_612,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5804,plain,
    ( u1_struct_0(k2_tsep_1(sK3,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_770])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1039,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1040,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_6524,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tsep_1(X0,sK2) = iProver_top
    | u1_struct_0(k2_tsep_1(sK3,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5804,c_27,c_30,c_32,c_1040])).

cnf(c_6525,plain,
    ( u1_struct_0(k2_tsep_1(sK3,X0,sK2)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6524])).

cnf(c_6536,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_6525])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_958,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_pre_topc(k2_tsep_1(sK3,sK1,X0),sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1287,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_933,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v1_pre_topc(k2_tsep_1(sK3,sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1419,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1059,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,X0),sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK3,sK1,X0))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v1_pre_topc(k2_tsep_1(sK3,sK1,X0))
    | u1_struct_0(k2_tsep_1(sK3,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2051,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_pre_topc(k2_tsep_1(sK3,sK1,sK2))
    | u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_2286,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6648,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6536,c_22,c_21,c_19,c_17,c_15,c_14,c_13,c_1039,c_1287,c_1419,c_2051,c_2286])).

cnf(c_7987,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7983,c_6648])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_36,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15834,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7987,c_28,c_36])).

cnf(c_15863,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_15834,c_6648])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_617,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1431,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_617])).

cnf(c_610,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_616,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2341,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_616])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3451,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2341,c_26,c_27])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_618,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3460,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3451,c_618])).

cnf(c_4976,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(X0),X1),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_3460])).

cnf(c_16407,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15863,c_4976])).

cnf(c_11,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12550,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12551,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12550])).

cnf(c_12553,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12551])).

cnf(c_973,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1337,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_1338,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1337])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_37,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_34,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

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
    inference(minisat,[status(thm)],[c_16407,c_12553,c_1338,c_37,c_34,c_33,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).


%------------------------------------------------------------------------------
