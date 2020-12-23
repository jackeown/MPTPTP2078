%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:08 EST 2020

% Result     : Theorem 19.46s
% Output     : CNFRefutation 19.46s
% Verified   : 
% Statistics : Number of formulae       :  177 (1235 expanded)
%              Number of clauses        :  125 ( 332 expanded)
%              Number of leaves         :   12 ( 414 expanded)
%              Depth                    :   21
%              Number of atoms          :  723 (11715 expanded)
%              Number of equality atoms :  217 ( 458 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f36,f35,f34,f33])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

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
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
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
    inference(equality_resolution,[],[f43])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_671,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1148,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_673,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1146,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_148,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_9,c_8,c_7])).

cnf(c_149,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_667,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_149])).

cnf(c_1152,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_5081,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1152])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5611,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5081,c_26,c_28,c_31])).

cnf(c_5612,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5611])).

cnf(c_5619,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_5612])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_683,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1136,plain,
    ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_4336,plain,
    ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1136])).

cnf(c_5237,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4336,c_26,c_28,c_31])).

cnf(c_5238,plain,
    ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5237])).

cnf(c_5245,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_5238])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5252,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5245,c_29])).

cnf(c_5621,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5619,c_5252])).

cnf(c_56585,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5621,c_29])).

cnf(c_5082,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1152])).

cnf(c_5683,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5082,c_26,c_28,c_29])).

cnf(c_5684,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5683])).

cnf(c_5690,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_5684])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_676,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1143,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_355,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_356,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_23])).

cnf(c_361,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_665,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_1154,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_687,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | k2_xboole_0(X0_44,X1_44) = X1_44 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1132,plain,
    ( k2_xboole_0(X0_44,X1_44) = X1_44
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_1986,plain,
    ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43)
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1132])).

cnf(c_4229,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1986])).

cnf(c_30,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_32,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4785,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4229,c_30,c_32])).

cnf(c_5694,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5690,c_4785])).

cnf(c_53529,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5694,c_31])).

cnf(c_56587,plain,
    ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_56585,c_53529])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_677,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1142,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_5078,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1152])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_685,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1470,plain,
    ( ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_1471,plain,
    ( m1_pre_topc(sK2,X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_1473,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_5293,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5078,c_28,c_31,c_32,c_33,c_1473])).

cnf(c_5294,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5293])).

cnf(c_5300,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK1)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_5294])).

cnf(c_4333,plain,
    ( k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1136])).

cnf(c_4961,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4333,c_28,c_31,c_32,c_33,c_1473])).

cnf(c_4962,plain,
    ( k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43)
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4961])).

cnf(c_4968,plain,
    ( k1_tsep_1(sK2,sK3,sK1) = k1_tsep_1(sK2,sK1,sK3)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_4962])).

cnf(c_5031,plain,
    ( k1_tsep_1(sK2,sK3,sK1) = k1_tsep_1(sK2,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4968,c_29])).

cnf(c_5302,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5300,c_5031])).

cnf(c_55047,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5302,c_29])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_686,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1133,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_55070,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),k2_xboole_0(X0_44,u1_struct_0(sK1))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_55047,c_1133])).

cnf(c_56757,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56587,c_55070])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_675,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1144,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_5080,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_1152])).

cnf(c_5575,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5080,c_26,c_28,c_33])).

cnf(c_5576,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5575])).

cnf(c_5583,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK1)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_5576])).

cnf(c_4335,plain,
    ( k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_1136])).

cnf(c_5062,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4335,c_26,c_28,c_33])).

cnf(c_5063,plain,
    ( k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5062])).

cnf(c_5070,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_5063])).

cnf(c_5145,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5070,c_29])).

cnf(c_5585,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5583,c_5145])).

cnf(c_55525,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5585,c_29])).

cnf(c_55527,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(demodulation,[status(thm)],[c_55525,c_55047])).

cnf(c_56760,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_56757,c_55527])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_335,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_336,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_338,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_23])).

cnf(c_339,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_666,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_2930,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_7121,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2930])).

cnf(c_7122,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7121])).

cnf(c_681,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1218,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,sK1,X0_43),X1_43)
    | ~ m1_pre_topc(sK1,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_43) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_2064,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_2065,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2064])).

cnf(c_1354,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK3,X0_43)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1509,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1510,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_14,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_36,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56760,c_7122,c_2065,c_1510,c_37,c_36,c_34,c_33,c_32,c_30,c_29,c_28,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.46/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.46/3.00  
% 19.46/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.46/3.00  
% 19.46/3.00  ------  iProver source info
% 19.46/3.00  
% 19.46/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.46/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.46/3.00  git: non_committed_changes: false
% 19.46/3.00  git: last_make_outside_of_git: false
% 19.46/3.00  
% 19.46/3.00  ------ 
% 19.46/3.00  
% 19.46/3.00  ------ Input Options
% 19.46/3.00  
% 19.46/3.00  --out_options                           all
% 19.46/3.00  --tptp_safe_out                         true
% 19.46/3.00  --problem_path                          ""
% 19.46/3.00  --include_path                          ""
% 19.46/3.00  --clausifier                            res/vclausify_rel
% 19.46/3.00  --clausifier_options                    ""
% 19.46/3.00  --stdin                                 false
% 19.46/3.00  --stats_out                             all
% 19.46/3.00  
% 19.46/3.00  ------ General Options
% 19.46/3.00  
% 19.46/3.00  --fof                                   false
% 19.46/3.00  --time_out_real                         305.
% 19.46/3.00  --time_out_virtual                      -1.
% 19.46/3.00  --symbol_type_check                     false
% 19.46/3.00  --clausify_out                          false
% 19.46/3.00  --sig_cnt_out                           false
% 19.46/3.00  --trig_cnt_out                          false
% 19.46/3.00  --trig_cnt_out_tolerance                1.
% 19.46/3.00  --trig_cnt_out_sk_spl                   false
% 19.46/3.00  --abstr_cl_out                          false
% 19.46/3.00  
% 19.46/3.00  ------ Global Options
% 19.46/3.00  
% 19.46/3.00  --schedule                              default
% 19.46/3.00  --add_important_lit                     false
% 19.46/3.00  --prop_solver_per_cl                    1000
% 19.46/3.00  --min_unsat_core                        false
% 19.46/3.00  --soft_assumptions                      false
% 19.46/3.00  --soft_lemma_size                       3
% 19.46/3.00  --prop_impl_unit_size                   0
% 19.46/3.00  --prop_impl_unit                        []
% 19.46/3.00  --share_sel_clauses                     true
% 19.46/3.00  --reset_solvers                         false
% 19.46/3.00  --bc_imp_inh                            [conj_cone]
% 19.46/3.00  --conj_cone_tolerance                   3.
% 19.46/3.00  --extra_neg_conj                        none
% 19.46/3.00  --large_theory_mode                     true
% 19.46/3.00  --prolific_symb_bound                   200
% 19.46/3.00  --lt_threshold                          2000
% 19.46/3.00  --clause_weak_htbl                      true
% 19.46/3.00  --gc_record_bc_elim                     false
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing Options
% 19.46/3.00  
% 19.46/3.00  --preprocessing_flag                    true
% 19.46/3.00  --time_out_prep_mult                    0.1
% 19.46/3.00  --splitting_mode                        input
% 19.46/3.00  --splitting_grd                         true
% 19.46/3.00  --splitting_cvd                         false
% 19.46/3.00  --splitting_cvd_svl                     false
% 19.46/3.00  --splitting_nvd                         32
% 19.46/3.00  --sub_typing                            true
% 19.46/3.00  --prep_gs_sim                           true
% 19.46/3.00  --prep_unflatten                        true
% 19.46/3.00  --prep_res_sim                          true
% 19.46/3.00  --prep_upred                            true
% 19.46/3.00  --prep_sem_filter                       exhaustive
% 19.46/3.00  --prep_sem_filter_out                   false
% 19.46/3.00  --pred_elim                             true
% 19.46/3.00  --res_sim_input                         true
% 19.46/3.00  --eq_ax_congr_red                       true
% 19.46/3.00  --pure_diseq_elim                       true
% 19.46/3.00  --brand_transform                       false
% 19.46/3.00  --non_eq_to_eq                          false
% 19.46/3.00  --prep_def_merge                        true
% 19.46/3.00  --prep_def_merge_prop_impl              false
% 19.46/3.00  --prep_def_merge_mbd                    true
% 19.46/3.00  --prep_def_merge_tr_red                 false
% 19.46/3.00  --prep_def_merge_tr_cl                  false
% 19.46/3.00  --smt_preprocessing                     true
% 19.46/3.00  --smt_ac_axioms                         fast
% 19.46/3.00  --preprocessed_out                      false
% 19.46/3.00  --preprocessed_stats                    false
% 19.46/3.00  
% 19.46/3.00  ------ Abstraction refinement Options
% 19.46/3.00  
% 19.46/3.00  --abstr_ref                             []
% 19.46/3.00  --abstr_ref_prep                        false
% 19.46/3.00  --abstr_ref_until_sat                   false
% 19.46/3.00  --abstr_ref_sig_restrict                funpre
% 19.46/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.46/3.00  --abstr_ref_under                       []
% 19.46/3.00  
% 19.46/3.00  ------ SAT Options
% 19.46/3.00  
% 19.46/3.00  --sat_mode                              false
% 19.46/3.00  --sat_fm_restart_options                ""
% 19.46/3.00  --sat_gr_def                            false
% 19.46/3.00  --sat_epr_types                         true
% 19.46/3.00  --sat_non_cyclic_types                  false
% 19.46/3.00  --sat_finite_models                     false
% 19.46/3.00  --sat_fm_lemmas                         false
% 19.46/3.00  --sat_fm_prep                           false
% 19.46/3.00  --sat_fm_uc_incr                        true
% 19.46/3.00  --sat_out_model                         small
% 19.46/3.00  --sat_out_clauses                       false
% 19.46/3.00  
% 19.46/3.00  ------ QBF Options
% 19.46/3.00  
% 19.46/3.00  --qbf_mode                              false
% 19.46/3.00  --qbf_elim_univ                         false
% 19.46/3.00  --qbf_dom_inst                          none
% 19.46/3.00  --qbf_dom_pre_inst                      false
% 19.46/3.00  --qbf_sk_in                             false
% 19.46/3.00  --qbf_pred_elim                         true
% 19.46/3.00  --qbf_split                             512
% 19.46/3.00  
% 19.46/3.00  ------ BMC1 Options
% 19.46/3.00  
% 19.46/3.00  --bmc1_incremental                      false
% 19.46/3.00  --bmc1_axioms                           reachable_all
% 19.46/3.00  --bmc1_min_bound                        0
% 19.46/3.00  --bmc1_max_bound                        -1
% 19.46/3.00  --bmc1_max_bound_default                -1
% 19.46/3.00  --bmc1_symbol_reachability              true
% 19.46/3.00  --bmc1_property_lemmas                  false
% 19.46/3.00  --bmc1_k_induction                      false
% 19.46/3.00  --bmc1_non_equiv_states                 false
% 19.46/3.00  --bmc1_deadlock                         false
% 19.46/3.00  --bmc1_ucm                              false
% 19.46/3.00  --bmc1_add_unsat_core                   none
% 19.46/3.00  --bmc1_unsat_core_children              false
% 19.46/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.46/3.00  --bmc1_out_stat                         full
% 19.46/3.00  --bmc1_ground_init                      false
% 19.46/3.00  --bmc1_pre_inst_next_state              false
% 19.46/3.00  --bmc1_pre_inst_state                   false
% 19.46/3.00  --bmc1_pre_inst_reach_state             false
% 19.46/3.00  --bmc1_out_unsat_core                   false
% 19.46/3.00  --bmc1_aig_witness_out                  false
% 19.46/3.00  --bmc1_verbose                          false
% 19.46/3.00  --bmc1_dump_clauses_tptp                false
% 19.46/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.46/3.00  --bmc1_dump_file                        -
% 19.46/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.46/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.46/3.00  --bmc1_ucm_extend_mode                  1
% 19.46/3.00  --bmc1_ucm_init_mode                    2
% 19.46/3.00  --bmc1_ucm_cone_mode                    none
% 19.46/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.46/3.00  --bmc1_ucm_relax_model                  4
% 19.46/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.46/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.46/3.00  --bmc1_ucm_layered_model                none
% 19.46/3.00  --bmc1_ucm_max_lemma_size               10
% 19.46/3.00  
% 19.46/3.00  ------ AIG Options
% 19.46/3.00  
% 19.46/3.00  --aig_mode                              false
% 19.46/3.00  
% 19.46/3.00  ------ Instantiation Options
% 19.46/3.00  
% 19.46/3.00  --instantiation_flag                    true
% 19.46/3.00  --inst_sos_flag                         true
% 19.46/3.00  --inst_sos_phase                        true
% 19.46/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.46/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.46/3.00  --inst_lit_sel_side                     num_symb
% 19.46/3.00  --inst_solver_per_active                1400
% 19.46/3.00  --inst_solver_calls_frac                1.
% 19.46/3.00  --inst_passive_queue_type               priority_queues
% 19.46/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.46/3.00  --inst_passive_queues_freq              [25;2]
% 19.46/3.00  --inst_dismatching                      true
% 19.46/3.00  --inst_eager_unprocessed_to_passive     true
% 19.46/3.00  --inst_prop_sim_given                   true
% 19.46/3.00  --inst_prop_sim_new                     false
% 19.46/3.00  --inst_subs_new                         false
% 19.46/3.00  --inst_eq_res_simp                      false
% 19.46/3.00  --inst_subs_given                       false
% 19.46/3.00  --inst_orphan_elimination               true
% 19.46/3.00  --inst_learning_loop_flag               true
% 19.46/3.00  --inst_learning_start                   3000
% 19.46/3.00  --inst_learning_factor                  2
% 19.46/3.00  --inst_start_prop_sim_after_learn       3
% 19.46/3.00  --inst_sel_renew                        solver
% 19.46/3.00  --inst_lit_activity_flag                true
% 19.46/3.00  --inst_restr_to_given                   false
% 19.46/3.00  --inst_activity_threshold               500
% 19.46/3.00  --inst_out_proof                        true
% 19.46/3.00  
% 19.46/3.00  ------ Resolution Options
% 19.46/3.00  
% 19.46/3.00  --resolution_flag                       true
% 19.46/3.00  --res_lit_sel                           adaptive
% 19.46/3.00  --res_lit_sel_side                      none
% 19.46/3.00  --res_ordering                          kbo
% 19.46/3.00  --res_to_prop_solver                    active
% 19.46/3.00  --res_prop_simpl_new                    false
% 19.46/3.00  --res_prop_simpl_given                  true
% 19.46/3.00  --res_passive_queue_type                priority_queues
% 19.46/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.46/3.00  --res_passive_queues_freq               [15;5]
% 19.46/3.00  --res_forward_subs                      full
% 19.46/3.00  --res_backward_subs                     full
% 19.46/3.00  --res_forward_subs_resolution           true
% 19.46/3.00  --res_backward_subs_resolution          true
% 19.46/3.00  --res_orphan_elimination                true
% 19.46/3.00  --res_time_limit                        2.
% 19.46/3.00  --res_out_proof                         true
% 19.46/3.00  
% 19.46/3.00  ------ Superposition Options
% 19.46/3.00  
% 19.46/3.00  --superposition_flag                    true
% 19.46/3.00  --sup_passive_queue_type                priority_queues
% 19.46/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.46/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.46/3.00  --demod_completeness_check              fast
% 19.46/3.00  --demod_use_ground                      true
% 19.46/3.00  --sup_to_prop_solver                    passive
% 19.46/3.00  --sup_prop_simpl_new                    true
% 19.46/3.00  --sup_prop_simpl_given                  true
% 19.46/3.00  --sup_fun_splitting                     true
% 19.46/3.00  --sup_smt_interval                      50000
% 19.46/3.00  
% 19.46/3.00  ------ Superposition Simplification Setup
% 19.46/3.00  
% 19.46/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.46/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.46/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.46/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.46/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.46/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.46/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.46/3.00  --sup_immed_triv                        [TrivRules]
% 19.46/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_immed_bw_main                     []
% 19.46/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.46/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.46/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_input_bw                          []
% 19.46/3.00  
% 19.46/3.00  ------ Combination Options
% 19.46/3.00  
% 19.46/3.00  --comb_res_mult                         3
% 19.46/3.00  --comb_sup_mult                         2
% 19.46/3.00  --comb_inst_mult                        10
% 19.46/3.00  
% 19.46/3.00  ------ Debug Options
% 19.46/3.00  
% 19.46/3.00  --dbg_backtrace                         false
% 19.46/3.00  --dbg_dump_prop_clauses                 false
% 19.46/3.00  --dbg_dump_prop_clauses_file            -
% 19.46/3.00  --dbg_out_stat                          false
% 19.46/3.00  ------ Parsing...
% 19.46/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.46/3.00  ------ Proving...
% 19.46/3.00  ------ Problem Properties 
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  clauses                                 25
% 19.46/3.00  conjectures                             11
% 19.46/3.00  EPR                                     11
% 19.46/3.00  Horn                                    17
% 19.46/3.00  unary                                   11
% 19.46/3.00  binary                                  2
% 19.46/3.00  lits                                    83
% 19.46/3.00  lits eq                                 6
% 19.46/3.00  fd_pure                                 0
% 19.46/3.00  fd_pseudo                               0
% 19.46/3.00  fd_cond                                 0
% 19.46/3.00  fd_pseudo_cond                          1
% 19.46/3.00  AC symbols                              0
% 19.46/3.00  
% 19.46/3.00  ------ Schedule dynamic 5 is on 
% 19.46/3.00  
% 19.46/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  ------ 
% 19.46/3.00  Current options:
% 19.46/3.00  ------ 
% 19.46/3.00  
% 19.46/3.00  ------ Input Options
% 19.46/3.00  
% 19.46/3.00  --out_options                           all
% 19.46/3.00  --tptp_safe_out                         true
% 19.46/3.00  --problem_path                          ""
% 19.46/3.00  --include_path                          ""
% 19.46/3.00  --clausifier                            res/vclausify_rel
% 19.46/3.00  --clausifier_options                    ""
% 19.46/3.00  --stdin                                 false
% 19.46/3.00  --stats_out                             all
% 19.46/3.00  
% 19.46/3.00  ------ General Options
% 19.46/3.00  
% 19.46/3.00  --fof                                   false
% 19.46/3.00  --time_out_real                         305.
% 19.46/3.00  --time_out_virtual                      -1.
% 19.46/3.00  --symbol_type_check                     false
% 19.46/3.00  --clausify_out                          false
% 19.46/3.00  --sig_cnt_out                           false
% 19.46/3.00  --trig_cnt_out                          false
% 19.46/3.00  --trig_cnt_out_tolerance                1.
% 19.46/3.00  --trig_cnt_out_sk_spl                   false
% 19.46/3.00  --abstr_cl_out                          false
% 19.46/3.00  
% 19.46/3.00  ------ Global Options
% 19.46/3.00  
% 19.46/3.00  --schedule                              default
% 19.46/3.00  --add_important_lit                     false
% 19.46/3.00  --prop_solver_per_cl                    1000
% 19.46/3.00  --min_unsat_core                        false
% 19.46/3.00  --soft_assumptions                      false
% 19.46/3.00  --soft_lemma_size                       3
% 19.46/3.00  --prop_impl_unit_size                   0
% 19.46/3.00  --prop_impl_unit                        []
% 19.46/3.00  --share_sel_clauses                     true
% 19.46/3.00  --reset_solvers                         false
% 19.46/3.00  --bc_imp_inh                            [conj_cone]
% 19.46/3.00  --conj_cone_tolerance                   3.
% 19.46/3.00  --extra_neg_conj                        none
% 19.46/3.00  --large_theory_mode                     true
% 19.46/3.00  --prolific_symb_bound                   200
% 19.46/3.00  --lt_threshold                          2000
% 19.46/3.00  --clause_weak_htbl                      true
% 19.46/3.00  --gc_record_bc_elim                     false
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing Options
% 19.46/3.00  
% 19.46/3.00  --preprocessing_flag                    true
% 19.46/3.00  --time_out_prep_mult                    0.1
% 19.46/3.00  --splitting_mode                        input
% 19.46/3.00  --splitting_grd                         true
% 19.46/3.00  --splitting_cvd                         false
% 19.46/3.00  --splitting_cvd_svl                     false
% 19.46/3.00  --splitting_nvd                         32
% 19.46/3.00  --sub_typing                            true
% 19.46/3.00  --prep_gs_sim                           true
% 19.46/3.00  --prep_unflatten                        true
% 19.46/3.00  --prep_res_sim                          true
% 19.46/3.00  --prep_upred                            true
% 19.46/3.00  --prep_sem_filter                       exhaustive
% 19.46/3.00  --prep_sem_filter_out                   false
% 19.46/3.00  --pred_elim                             true
% 19.46/3.00  --res_sim_input                         true
% 19.46/3.00  --eq_ax_congr_red                       true
% 19.46/3.00  --pure_diseq_elim                       true
% 19.46/3.00  --brand_transform                       false
% 19.46/3.00  --non_eq_to_eq                          false
% 19.46/3.00  --prep_def_merge                        true
% 19.46/3.00  --prep_def_merge_prop_impl              false
% 19.46/3.00  --prep_def_merge_mbd                    true
% 19.46/3.00  --prep_def_merge_tr_red                 false
% 19.46/3.00  --prep_def_merge_tr_cl                  false
% 19.46/3.00  --smt_preprocessing                     true
% 19.46/3.00  --smt_ac_axioms                         fast
% 19.46/3.00  --preprocessed_out                      false
% 19.46/3.00  --preprocessed_stats                    false
% 19.46/3.00  
% 19.46/3.00  ------ Abstraction refinement Options
% 19.46/3.00  
% 19.46/3.00  --abstr_ref                             []
% 19.46/3.00  --abstr_ref_prep                        false
% 19.46/3.00  --abstr_ref_until_sat                   false
% 19.46/3.00  --abstr_ref_sig_restrict                funpre
% 19.46/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.46/3.00  --abstr_ref_under                       []
% 19.46/3.00  
% 19.46/3.00  ------ SAT Options
% 19.46/3.00  
% 19.46/3.00  --sat_mode                              false
% 19.46/3.00  --sat_fm_restart_options                ""
% 19.46/3.00  --sat_gr_def                            false
% 19.46/3.00  --sat_epr_types                         true
% 19.46/3.00  --sat_non_cyclic_types                  false
% 19.46/3.00  --sat_finite_models                     false
% 19.46/3.00  --sat_fm_lemmas                         false
% 19.46/3.00  --sat_fm_prep                           false
% 19.46/3.00  --sat_fm_uc_incr                        true
% 19.46/3.00  --sat_out_model                         small
% 19.46/3.00  --sat_out_clauses                       false
% 19.46/3.00  
% 19.46/3.00  ------ QBF Options
% 19.46/3.00  
% 19.46/3.00  --qbf_mode                              false
% 19.46/3.00  --qbf_elim_univ                         false
% 19.46/3.00  --qbf_dom_inst                          none
% 19.46/3.00  --qbf_dom_pre_inst                      false
% 19.46/3.00  --qbf_sk_in                             false
% 19.46/3.00  --qbf_pred_elim                         true
% 19.46/3.00  --qbf_split                             512
% 19.46/3.00  
% 19.46/3.00  ------ BMC1 Options
% 19.46/3.00  
% 19.46/3.00  --bmc1_incremental                      false
% 19.46/3.00  --bmc1_axioms                           reachable_all
% 19.46/3.00  --bmc1_min_bound                        0
% 19.46/3.00  --bmc1_max_bound                        -1
% 19.46/3.00  --bmc1_max_bound_default                -1
% 19.46/3.00  --bmc1_symbol_reachability              true
% 19.46/3.00  --bmc1_property_lemmas                  false
% 19.46/3.00  --bmc1_k_induction                      false
% 19.46/3.00  --bmc1_non_equiv_states                 false
% 19.46/3.00  --bmc1_deadlock                         false
% 19.46/3.00  --bmc1_ucm                              false
% 19.46/3.00  --bmc1_add_unsat_core                   none
% 19.46/3.00  --bmc1_unsat_core_children              false
% 19.46/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.46/3.00  --bmc1_out_stat                         full
% 19.46/3.00  --bmc1_ground_init                      false
% 19.46/3.00  --bmc1_pre_inst_next_state              false
% 19.46/3.00  --bmc1_pre_inst_state                   false
% 19.46/3.00  --bmc1_pre_inst_reach_state             false
% 19.46/3.00  --bmc1_out_unsat_core                   false
% 19.46/3.00  --bmc1_aig_witness_out                  false
% 19.46/3.00  --bmc1_verbose                          false
% 19.46/3.00  --bmc1_dump_clauses_tptp                false
% 19.46/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.46/3.00  --bmc1_dump_file                        -
% 19.46/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.46/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.46/3.00  --bmc1_ucm_extend_mode                  1
% 19.46/3.00  --bmc1_ucm_init_mode                    2
% 19.46/3.00  --bmc1_ucm_cone_mode                    none
% 19.46/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.46/3.00  --bmc1_ucm_relax_model                  4
% 19.46/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.46/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.46/3.00  --bmc1_ucm_layered_model                none
% 19.46/3.00  --bmc1_ucm_max_lemma_size               10
% 19.46/3.00  
% 19.46/3.00  ------ AIG Options
% 19.46/3.00  
% 19.46/3.00  --aig_mode                              false
% 19.46/3.00  
% 19.46/3.00  ------ Instantiation Options
% 19.46/3.00  
% 19.46/3.00  --instantiation_flag                    true
% 19.46/3.00  --inst_sos_flag                         true
% 19.46/3.00  --inst_sos_phase                        true
% 19.46/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.46/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.46/3.00  --inst_lit_sel_side                     none
% 19.46/3.00  --inst_solver_per_active                1400
% 19.46/3.00  --inst_solver_calls_frac                1.
% 19.46/3.00  --inst_passive_queue_type               priority_queues
% 19.46/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.46/3.00  --inst_passive_queues_freq              [25;2]
% 19.46/3.00  --inst_dismatching                      true
% 19.46/3.00  --inst_eager_unprocessed_to_passive     true
% 19.46/3.00  --inst_prop_sim_given                   true
% 19.46/3.00  --inst_prop_sim_new                     false
% 19.46/3.00  --inst_subs_new                         false
% 19.46/3.00  --inst_eq_res_simp                      false
% 19.46/3.00  --inst_subs_given                       false
% 19.46/3.00  --inst_orphan_elimination               true
% 19.46/3.00  --inst_learning_loop_flag               true
% 19.46/3.00  --inst_learning_start                   3000
% 19.46/3.00  --inst_learning_factor                  2
% 19.46/3.00  --inst_start_prop_sim_after_learn       3
% 19.46/3.00  --inst_sel_renew                        solver
% 19.46/3.00  --inst_lit_activity_flag                true
% 19.46/3.00  --inst_restr_to_given                   false
% 19.46/3.00  --inst_activity_threshold               500
% 19.46/3.00  --inst_out_proof                        true
% 19.46/3.00  
% 19.46/3.00  ------ Resolution Options
% 19.46/3.00  
% 19.46/3.00  --resolution_flag                       false
% 19.46/3.00  --res_lit_sel                           adaptive
% 19.46/3.00  --res_lit_sel_side                      none
% 19.46/3.00  --res_ordering                          kbo
% 19.46/3.00  --res_to_prop_solver                    active
% 19.46/3.00  --res_prop_simpl_new                    false
% 19.46/3.00  --res_prop_simpl_given                  true
% 19.46/3.00  --res_passive_queue_type                priority_queues
% 19.46/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.46/3.00  --res_passive_queues_freq               [15;5]
% 19.46/3.00  --res_forward_subs                      full
% 19.46/3.00  --res_backward_subs                     full
% 19.46/3.00  --res_forward_subs_resolution           true
% 19.46/3.00  --res_backward_subs_resolution          true
% 19.46/3.00  --res_orphan_elimination                true
% 19.46/3.00  --res_time_limit                        2.
% 19.46/3.00  --res_out_proof                         true
% 19.46/3.00  
% 19.46/3.00  ------ Superposition Options
% 19.46/3.00  
% 19.46/3.00  --superposition_flag                    true
% 19.46/3.00  --sup_passive_queue_type                priority_queues
% 19.46/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.46/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.46/3.00  --demod_completeness_check              fast
% 19.46/3.00  --demod_use_ground                      true
% 19.46/3.00  --sup_to_prop_solver                    passive
% 19.46/3.00  --sup_prop_simpl_new                    true
% 19.46/3.00  --sup_prop_simpl_given                  true
% 19.46/3.00  --sup_fun_splitting                     true
% 19.46/3.00  --sup_smt_interval                      50000
% 19.46/3.00  
% 19.46/3.00  ------ Superposition Simplification Setup
% 19.46/3.00  
% 19.46/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.46/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.46/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.46/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.46/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.46/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.46/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.46/3.00  --sup_immed_triv                        [TrivRules]
% 19.46/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_immed_bw_main                     []
% 19.46/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.46/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.46/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.46/3.00  --sup_input_bw                          []
% 19.46/3.00  
% 19.46/3.00  ------ Combination Options
% 19.46/3.00  
% 19.46/3.00  --comb_res_mult                         3
% 19.46/3.00  --comb_sup_mult                         2
% 19.46/3.00  --comb_inst_mult                        10
% 19.46/3.00  
% 19.46/3.00  ------ Debug Options
% 19.46/3.00  
% 19.46/3.00  --dbg_backtrace                         false
% 19.46/3.00  --dbg_dump_prop_clauses                 false
% 19.46/3.00  --dbg_dump_prop_clauses_file            -
% 19.46/3.00  --dbg_out_stat                          false
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  ------ Proving...
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  % SZS status Theorem for theBenchmark.p
% 19.46/3.00  
% 19.46/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.46/3.00  
% 19.46/3.00  fof(f11,conjecture,(
% 19.46/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f12,negated_conjecture,(
% 19.46/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 19.46/3.00    inference(negated_conjecture,[],[f11])).
% 19.46/3.00  
% 19.46/3.00  fof(f29,plain,(
% 19.46/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.46/3.00    inference(ennf_transformation,[],[f12])).
% 19.46/3.00  
% 19.46/3.00  fof(f30,plain,(
% 19.46/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.46/3.00    inference(flattening,[],[f29])).
% 19.46/3.00  
% 19.46/3.00  fof(f36,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 19.46/3.00    introduced(choice_axiom,[])).
% 19.46/3.00  
% 19.46/3.00  fof(f35,plain,(
% 19.46/3.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 19.46/3.00    introduced(choice_axiom,[])).
% 19.46/3.00  
% 19.46/3.00  fof(f34,plain,(
% 19.46/3.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 19.46/3.00    introduced(choice_axiom,[])).
% 19.46/3.00  
% 19.46/3.00  fof(f33,plain,(
% 19.46/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 19.46/3.00    introduced(choice_axiom,[])).
% 19.46/3.00  
% 19.46/3.00  fof(f37,plain,(
% 19.46/3.00    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 19.46/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f36,f35,f34,f33])).
% 19.46/3.00  
% 19.46/3.00  fof(f56,plain,(
% 19.46/3.00    m1_pre_topc(sK1,sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f58,plain,(
% 19.46/3.00    m1_pre_topc(sK2,sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f6,axiom,(
% 19.46/3.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f19,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.46/3.00    inference(ennf_transformation,[],[f6])).
% 19.46/3.00  
% 19.46/3.00  fof(f20,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.46/3.00    inference(flattening,[],[f19])).
% 19.46/3.00  
% 19.46/3.00  fof(f31,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.46/3.00    inference(nnf_transformation,[],[f20])).
% 19.46/3.00  
% 19.46/3.00  fof(f43,plain,(
% 19.46/3.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f31])).
% 19.46/3.00  
% 19.46/3.00  fof(f64,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(equality_resolution,[],[f43])).
% 19.46/3.00  
% 19.46/3.00  fof(f7,axiom,(
% 19.46/3.00    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f21,plain,(
% 19.46/3.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.46/3.00    inference(ennf_transformation,[],[f7])).
% 19.46/3.00  
% 19.46/3.00  fof(f22,plain,(
% 19.46/3.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.46/3.00    inference(flattening,[],[f21])).
% 19.46/3.00  
% 19.46/3.00  fof(f45,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f22])).
% 19.46/3.00  
% 19.46/3.00  fof(f46,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f22])).
% 19.46/3.00  
% 19.46/3.00  fof(f47,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f22])).
% 19.46/3.00  
% 19.46/3.00  fof(f52,plain,(
% 19.46/3.00    ~v2_struct_0(sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f54,plain,(
% 19.46/3.00    l1_pre_topc(sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f57,plain,(
% 19.46/3.00    ~v2_struct_0(sK2)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f5,axiom,(
% 19.46/3.00    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f17,plain,(
% 19.46/3.00    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.46/3.00    inference(ennf_transformation,[],[f5])).
% 19.46/3.00  
% 19.46/3.00  fof(f18,plain,(
% 19.46/3.00    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.46/3.00    inference(flattening,[],[f17])).
% 19.46/3.00  
% 19.46/3.00  fof(f42,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f18])).
% 19.46/3.00  
% 19.46/3.00  fof(f55,plain,(
% 19.46/3.00    ~v2_struct_0(sK1)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f61,plain,(
% 19.46/3.00    m1_pre_topc(sK1,sK2)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f10,axiom,(
% 19.46/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f27,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.46/3.00    inference(ennf_transformation,[],[f10])).
% 19.46/3.00  
% 19.46/3.00  fof(f28,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.46/3.00    inference(flattening,[],[f27])).
% 19.46/3.00  
% 19.46/3.00  fof(f32,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.46/3.00    inference(nnf_transformation,[],[f28])).
% 19.46/3.00  
% 19.46/3.00  fof(f51,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f32])).
% 19.46/3.00  
% 19.46/3.00  fof(f53,plain,(
% 19.46/3.00    v2_pre_topc(sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f1,axiom,(
% 19.46/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f13,plain,(
% 19.46/3.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.46/3.00    inference(ennf_transformation,[],[f1])).
% 19.46/3.00  
% 19.46/3.00  fof(f38,plain,(
% 19.46/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f13])).
% 19.46/3.00  
% 19.46/3.00  fof(f62,plain,(
% 19.46/3.00    m1_pre_topc(sK3,sK2)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f59,plain,(
% 19.46/3.00    ~v2_struct_0(sK3)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f3,axiom,(
% 19.46/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f15,plain,(
% 19.46/3.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.46/3.00    inference(ennf_transformation,[],[f3])).
% 19.46/3.00  
% 19.46/3.00  fof(f40,plain,(
% 19.46/3.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f15])).
% 19.46/3.00  
% 19.46/3.00  fof(f2,axiom,(
% 19.46/3.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 19.46/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.46/3.00  
% 19.46/3.00  fof(f14,plain,(
% 19.46/3.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 19.46/3.00    inference(ennf_transformation,[],[f2])).
% 19.46/3.00  
% 19.46/3.00  fof(f39,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f14])).
% 19.46/3.00  
% 19.46/3.00  fof(f60,plain,(
% 19.46/3.00    m1_pre_topc(sK3,sK0)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  fof(f50,plain,(
% 19.46/3.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.46/3.00    inference(cnf_transformation,[],[f32])).
% 19.46/3.00  
% 19.46/3.00  fof(f63,plain,(
% 19.46/3.00    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 19.46/3.00    inference(cnf_transformation,[],[f37])).
% 19.46/3.00  
% 19.46/3.00  cnf(c_21,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK1,sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_671,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK1,sK0) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_21]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1148,plain,
% 19.46/3.00      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_19,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_673,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_19]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1146,plain,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_6,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 19.46/3.00      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.46/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_9,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 19.46/3.00      | ~ l1_pre_topc(X1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_8,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | ~ l1_pre_topc(X1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_7,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | ~ l1_pre_topc(X1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_148,plain,
% 19.46/3.00      ( v2_struct_0(X2)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_6,c_9,c_8,c_7]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_149,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_148]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_667,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ m1_pre_topc(X2_43,X1_43)
% 19.46/3.00      | v2_struct_0(X0_43)
% 19.46/3.00      | v2_struct_0(X1_43)
% 19.46/3.00      | v2_struct_0(X2_43)
% 19.46/3.00      | ~ l1_pre_topc(X1_43)
% 19.46/3.00      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_149]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1152,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 19.46/3.00      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 19.46/3.00      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(X1_43) = iProver_top
% 19.46/3.00      | v2_struct_0(X2_43) = iProver_top
% 19.46/3.00      | l1_pre_topc(X0_43) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5081,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1146,c_1152]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_25,negated_conjecture,
% 19.46/3.00      ( ~ v2_struct_0(sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_26,plain,
% 19.46/3.00      ( v2_struct_0(sK0) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_23,negated_conjecture,
% 19.46/3.00      ( l1_pre_topc(sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_28,plain,
% 19.46/3.00      ( l1_pre_topc(sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_20,negated_conjecture,
% 19.46/3.00      ( ~ v2_struct_0(sK2) ),
% 19.46/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_31,plain,
% 19.46/3.00      ( v2_struct_0(sK2) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5611,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5081,c_26,c_28,c_31]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5612,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK2,X0_43)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5611]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5619,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1148,c_5612]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | v2_struct_0(X1)
% 19.46/3.00      | v2_struct_0(X0)
% 19.46/3.00      | v2_struct_0(X2)
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
% 19.46/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_683,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ m1_pre_topc(X2_43,X1_43)
% 19.46/3.00      | v2_struct_0(X0_43)
% 19.46/3.00      | v2_struct_0(X1_43)
% 19.46/3.00      | v2_struct_0(X2_43)
% 19.46/3.00      | ~ l1_pre_topc(X1_43)
% 19.46/3.00      | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_4]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1136,plain,
% 19.46/3.00      ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
% 19.46/3.00      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 19.46/3.00      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(X2_43) = iProver_top
% 19.46/3.00      | v2_struct_0(X1_43) = iProver_top
% 19.46/3.00      | l1_pre_topc(X0_43) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4336,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1146,c_1136]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5237,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_4336,c_26,c_28,c_31]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5238,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5237]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5245,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1148,c_5238]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_22,negated_conjecture,
% 19.46/3.00      ( ~ v2_struct_0(sK1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_29,plain,
% 19.46/3.00      ( v2_struct_0(sK1) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5252,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5245,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5621,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_5619,c_5252]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_56585,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5621,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5082,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1148,c_1152]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5683,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5082,c_26,c_28,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5684,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5683]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5690,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1146,c_5684]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_16,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK1,sK2) ),
% 19.46/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_676,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK1,sK2) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_16]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1143,plain,
% 19.46/3.00      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_12,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | ~ m1_pre_topc(X0,X2)
% 19.46/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.46/3.00      | ~ v2_pre_topc(X1)
% 19.46/3.00      | ~ l1_pre_topc(X1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_24,negated_conjecture,
% 19.46/3.00      ( v2_pre_topc(sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_355,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | ~ m1_pre_topc(X0,X2)
% 19.46/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | sK0 != X1 ),
% 19.46/3.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_356,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.46/3.00      | ~ l1_pre_topc(sK0) ),
% 19.46/3.00      inference(unflattening,[status(thm)],[c_355]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_360,plain,
% 19.46/3.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X0,X1) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_356,c_23]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_361,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_360]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_665,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ m1_pre_topc(X0_43,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1_43,sK0)
% 19.46/3.00      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_361]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1154,plain,
% 19.46/3.00      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 19.46/3.00      | m1_pre_topc(X1_43,sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_0,plain,
% 19.46/3.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.46/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_687,plain,
% 19.46/3.00      ( ~ r1_tarski(X0_44,X1_44) | k2_xboole_0(X0_44,X1_44) = X1_44 ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_0]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1132,plain,
% 19.46/3.00      ( k2_xboole_0(X0_44,X1_44) = X1_44
% 19.46/3.00      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1986,plain,
% 19.46/3.00      ( k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) = u1_struct_0(X1_43)
% 19.46/3.00      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 19.46/3.00      | m1_pre_topc(X1_43,sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1154,c_1132]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4229,plain,
% 19.46/3.00      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2)
% 19.46/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1143,c_1986]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_30,plain,
% 19.46/3.00      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_32,plain,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4785,plain,
% 19.46/3.00      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(sK2) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_4229,c_30,c_32]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5694,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_5690,c_4785]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_53529,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5694,c_31]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_56587,plain,
% 19.46/3.00      ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) = u1_struct_0(sK2) ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_56585,c_53529]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_15,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK3,sK2) ),
% 19.46/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_677,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK3,sK2) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_15]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1142,plain,
% 19.46/3.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5078,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top
% 19.46/3.00      | v2_struct_0(sK3) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1142,c_1152]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_18,negated_conjecture,
% 19.46/3.00      ( ~ v2_struct_0(sK3) ),
% 19.46/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_33,plain,
% 19.46/3.00      ( v2_struct_0(sK3) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_2,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_685,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ l1_pre_topc(X1_43)
% 19.46/3.00      | l1_pre_topc(X0_43) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_2]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1470,plain,
% 19.46/3.00      ( ~ m1_pre_topc(sK2,X0_43)
% 19.46/3.00      | ~ l1_pre_topc(X0_43)
% 19.46/3.00      | l1_pre_topc(sK2) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_685]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1471,plain,
% 19.46/3.00      ( m1_pre_topc(sK2,X0_43) != iProver_top
% 19.46/3.00      | l1_pre_topc(X0_43) != iProver_top
% 19.46/3.00      | l1_pre_topc(sK2) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1473,plain,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.46/3.00      | l1_pre_topc(sK2) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_1471]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5293,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5078,c_28,c_31,c_32,c_33,c_1473]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5294,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK2,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5293]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5300,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK2,sK3,sK1)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1143,c_5294]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4333,plain,
% 19.46/3.00      ( k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK2) = iProver_top
% 19.46/3.00      | v2_struct_0(sK3) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1142,c_1136]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4961,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_4333,c_28,c_31,c_32,c_33,c_1473]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4962,plain,
% 19.46/3.00      ( k1_tsep_1(sK2,X0_43,sK3) = k1_tsep_1(sK2,sK3,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_4961]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4968,plain,
% 19.46/3.00      ( k1_tsep_1(sK2,sK3,sK1) = k1_tsep_1(sK2,sK1,sK3)
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1143,c_4962]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5031,plain,
% 19.46/3.00      ( k1_tsep_1(sK2,sK3,sK1) = k1_tsep_1(sK2,sK1,sK3) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_4968,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5302,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_5300,c_5031]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_55047,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5302,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1,plain,
% 19.46/3.00      ( ~ r1_tarski(X0,X1)
% 19.46/3.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 19.46/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_686,plain,
% 19.46/3.00      ( ~ r1_tarski(X0_44,X1_44)
% 19.46/3.00      | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_1]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1133,plain,
% 19.46/3.00      ( r1_tarski(X0_44,X1_44) != iProver_top
% 19.46/3.00      | r1_tarski(k2_xboole_0(X0_44,X2_44),k2_xboole_0(X1_44,X2_44)) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_55070,plain,
% 19.46/3.00      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),k2_xboole_0(X0_44,u1_struct_0(sK1))) = iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),X0_44) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_55047,c_1133]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_56757,plain,
% 19.46/3.00      ( r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2)) = iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_56587,c_55070]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_17,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK3,sK0) ),
% 19.46/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_675,negated_conjecture,
% 19.46/3.00      ( m1_pre_topc(sK3,sK0) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_17]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1144,plain,
% 19.46/3.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5080,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK3) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1144,c_1152]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5575,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5080,c_26,c_28,c_33]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5576,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK3,X0_43)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5575]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5583,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK1)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1148,c_5576]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_4335,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | v2_struct_0(sK3) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1144,c_1136]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5062,plain,
% 19.46/3.00      ( v2_struct_0(X0_43) = iProver_top
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_4335,c_26,c_28,c_33]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5063,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,X0_43,sK3) = k1_tsep_1(sK0,sK3,X0_43)
% 19.46/3.00      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(X0_43) = iProver_top ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_5062]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5070,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(superposition,[status(thm)],[c_1148,c_5063]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5145,plain,
% 19.46/3.00      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5070,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_5585,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_5583,c_5145]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_55525,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_5585,c_29]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_55527,plain,
% 19.46/3.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 19.46/3.00      inference(demodulation,[status(thm)],[c_55525,c_55047]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_56760,plain,
% 19.46/3.00      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 19.46/3.00      inference(light_normalisation,[status(thm)],[c_56757,c_55527]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_13,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | m1_pre_topc(X0,X2)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.46/3.00      | ~ v2_pre_topc(X1)
% 19.46/3.00      | ~ l1_pre_topc(X1) ),
% 19.46/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_335,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X2,X1)
% 19.46/3.00      | m1_pre_topc(X0,X2)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.46/3.00      | ~ l1_pre_topc(X1)
% 19.46/3.00      | sK0 != X1 ),
% 19.46/3.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_336,plain,
% 19.46/3.00      ( m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.46/3.00      | ~ l1_pre_topc(sK0) ),
% 19.46/3.00      inference(unflattening,[status(thm)],[c_335]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_338,plain,
% 19.46/3.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | m1_pre_topc(X0,X1) ),
% 19.46/3.00      inference(global_propositional_subsumption,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_336,c_23]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_339,plain,
% 19.46/3.00      ( m1_pre_topc(X0,X1)
% 19.46/3.00      | ~ m1_pre_topc(X0,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1,sK0)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 19.46/3.00      inference(renaming,[status(thm)],[c_338]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_666,plain,
% 19.46/3.00      ( m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ m1_pre_topc(X0_43,sK0)
% 19.46/3.00      | ~ m1_pre_topc(X1_43,sK0)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_339]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_2930,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,sK0)
% 19.46/3.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_43)
% 19.46/3.00      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_666]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_7121,plain,
% 19.46/3.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 19.46/3.00      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.46/3.00      | ~ m1_pre_topc(sK2,sK0)
% 19.46/3.00      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_2930]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_7122,plain,
% 19.46/3.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
% 19.46/3.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_7121]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_681,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | ~ m1_pre_topc(X2_43,X1_43)
% 19.46/3.00      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 19.46/3.00      | v2_struct_0(X0_43)
% 19.46/3.00      | v2_struct_0(X1_43)
% 19.46/3.00      | v2_struct_0(X2_43)
% 19.46/3.00      | ~ l1_pre_topc(X1_43) ),
% 19.46/3.00      inference(subtyping,[status(esa)],[c_7]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1218,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.46/3.00      | m1_pre_topc(k1_tsep_1(X1_43,sK1,X0_43),X1_43)
% 19.46/3.00      | ~ m1_pre_topc(sK1,X1_43)
% 19.46/3.00      | v2_struct_0(X1_43)
% 19.46/3.00      | v2_struct_0(X0_43)
% 19.46/3.00      | v2_struct_0(sK1)
% 19.46/3.00      | ~ l1_pre_topc(X1_43) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_681]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_2064,plain,
% 19.46/3.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.46/3.00      | ~ m1_pre_topc(sK3,sK0)
% 19.46/3.00      | ~ m1_pre_topc(sK1,sK0)
% 19.46/3.00      | v2_struct_0(sK3)
% 19.46/3.00      | v2_struct_0(sK1)
% 19.46/3.00      | v2_struct_0(sK0)
% 19.46/3.00      | ~ l1_pre_topc(sK0) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_1218]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_2065,plain,
% 19.46/3.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 19.46/3.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 19.46/3.00      | v2_struct_0(sK3) = iProver_top
% 19.46/3.00      | v2_struct_0(sK1) = iProver_top
% 19.46/3.00      | v2_struct_0(sK0) = iProver_top
% 19.46/3.00      | l1_pre_topc(sK0) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_2064]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1354,plain,
% 19.46/3.00      ( ~ m1_pre_topc(X0_43,sK0)
% 19.46/3.00      | ~ m1_pre_topc(sK3,X0_43)
% 19.46/3.00      | ~ m1_pre_topc(sK3,sK0)
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_665]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1509,plain,
% 19.46/3.00      ( ~ m1_pre_topc(sK2,sK0)
% 19.46/3.00      | ~ m1_pre_topc(sK3,sK2)
% 19.46/3.00      | ~ m1_pre_topc(sK3,sK0)
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 19.46/3.00      inference(instantiation,[status(thm)],[c_1354]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_1510,plain,
% 19.46/3.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.46/3.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 19.46/3.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 19.46/3.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_14,negated_conjecture,
% 19.46/3.00      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 19.46/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_37,plain,
% 19.46/3.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_36,plain,
% 19.46/3.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(c_34,plain,
% 19.46/3.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 19.46/3.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.46/3.00  
% 19.46/3.00  cnf(contradiction,plain,
% 19.46/3.00      ( $false ),
% 19.46/3.00      inference(minisat,
% 19.46/3.00                [status(thm)],
% 19.46/3.00                [c_56760,c_7122,c_2065,c_1510,c_37,c_36,c_34,c_33,c_32,
% 19.46/3.00                 c_30,c_29,c_28,c_26]) ).
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.46/3.00  
% 19.46/3.00  ------                               Statistics
% 19.46/3.00  
% 19.46/3.00  ------ General
% 19.46/3.00  
% 19.46/3.00  abstr_ref_over_cycles:                  0
% 19.46/3.00  abstr_ref_under_cycles:                 0
% 19.46/3.00  gc_basic_clause_elim:                   0
% 19.46/3.00  forced_gc_time:                         0
% 19.46/3.00  parsing_time:                           0.007
% 19.46/3.00  unif_index_cands_time:                  0.
% 19.46/3.00  unif_index_add_time:                    0.
% 19.46/3.00  orderings_time:                         0.
% 19.46/3.00  out_proof_time:                         0.024
% 19.46/3.00  total_time:                             2.185
% 19.46/3.00  num_of_symbols:                         49
% 19.46/3.00  num_of_terms:                           85399
% 19.46/3.00  
% 19.46/3.00  ------ Preprocessing
% 19.46/3.00  
% 19.46/3.00  num_of_splits:                          0
% 19.46/3.00  num_of_split_atoms:                     0
% 19.46/3.00  num_of_reused_defs:                     0
% 19.46/3.00  num_eq_ax_congr_red:                    3
% 19.46/3.00  num_of_sem_filtered_clauses:            1
% 19.46/3.00  num_of_subtypes:                        3
% 19.46/3.00  monotx_restored_types:                  0
% 19.46/3.00  sat_num_of_epr_types:                   0
% 19.46/3.00  sat_num_of_non_cyclic_types:            0
% 19.46/3.00  sat_guarded_non_collapsed_types:        2
% 19.46/3.00  num_pure_diseq_elim:                    0
% 19.46/3.00  simp_replaced_by:                       0
% 19.46/3.00  res_preprocessed:                       130
% 19.46/3.00  prep_upred:                             0
% 19.46/3.00  prep_unflattend:                        6
% 19.46/3.00  smt_new_axioms:                         0
% 19.46/3.00  pred_elim_cands:                        5
% 19.46/3.00  pred_elim:                              1
% 19.46/3.00  pred_elim_cl:                           1
% 19.46/3.00  pred_elim_cycles:                       4
% 19.46/3.00  merged_defs:                            0
% 19.46/3.00  merged_defs_ncl:                        0
% 19.46/3.00  bin_hyper_res:                          0
% 19.46/3.00  prep_cycles:                            4
% 19.46/3.00  pred_elim_time:                         0.005
% 19.46/3.00  splitting_time:                         0.
% 19.46/3.00  sem_filter_time:                        0.
% 19.46/3.00  monotx_time:                            0.
% 19.46/3.00  subtype_inf_time:                       0.
% 19.46/3.00  
% 19.46/3.00  ------ Problem properties
% 19.46/3.00  
% 19.46/3.00  clauses:                                25
% 19.46/3.00  conjectures:                            11
% 19.46/3.00  epr:                                    11
% 19.46/3.00  horn:                                   17
% 19.46/3.00  ground:                                 11
% 19.46/3.00  unary:                                  11
% 19.46/3.00  binary:                                 2
% 19.46/3.00  lits:                                   83
% 19.46/3.00  lits_eq:                                6
% 19.46/3.00  fd_pure:                                0
% 19.46/3.00  fd_pseudo:                              0
% 19.46/3.00  fd_cond:                                0
% 19.46/3.00  fd_pseudo_cond:                         1
% 19.46/3.00  ac_symbols:                             0
% 19.46/3.00  
% 19.46/3.00  ------ Propositional Solver
% 19.46/3.00  
% 19.46/3.00  prop_solver_calls:                      33
% 19.46/3.00  prop_fast_solver_calls:                 2708
% 19.46/3.00  smt_solver_calls:                       0
% 19.46/3.00  smt_fast_solver_calls:                  0
% 19.46/3.00  prop_num_of_clauses:                    24331
% 19.46/3.00  prop_preprocess_simplified:             37345
% 19.46/3.00  prop_fo_subsumed:                       249
% 19.46/3.00  prop_solver_time:                       0.
% 19.46/3.00  smt_solver_time:                        0.
% 19.46/3.00  smt_fast_solver_time:                   0.
% 19.46/3.00  prop_fast_solver_time:                  0.
% 19.46/3.00  prop_unsat_core_time:                   0.003
% 19.46/3.00  
% 19.46/3.00  ------ QBF
% 19.46/3.00  
% 19.46/3.00  qbf_q_res:                              0
% 19.46/3.00  qbf_num_tautologies:                    0
% 19.46/3.00  qbf_prep_cycles:                        0
% 19.46/3.00  
% 19.46/3.00  ------ BMC1
% 19.46/3.00  
% 19.46/3.00  bmc1_current_bound:                     -1
% 19.46/3.00  bmc1_last_solved_bound:                 -1
% 19.46/3.00  bmc1_unsat_core_size:                   -1
% 19.46/3.00  bmc1_unsat_core_parents_size:           -1
% 19.46/3.00  bmc1_merge_next_fun:                    0
% 19.46/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.46/3.00  
% 19.46/3.00  ------ Instantiation
% 19.46/3.00  
% 19.46/3.00  inst_num_of_clauses:                    5253
% 19.46/3.00  inst_num_in_passive:                    2856
% 19.46/3.00  inst_num_in_active:                     2059
% 19.46/3.00  inst_num_in_unprocessed:                338
% 19.46/3.00  inst_num_of_loops:                      2250
% 19.46/3.00  inst_num_of_learning_restarts:          0
% 19.46/3.00  inst_num_moves_active_passive:          191
% 19.46/3.00  inst_lit_activity:                      0
% 19.46/3.00  inst_lit_activity_moves:                3
% 19.46/3.00  inst_num_tautologies:                   0
% 19.46/3.00  inst_num_prop_implied:                  0
% 19.46/3.00  inst_num_existing_simplified:           0
% 19.46/3.00  inst_num_eq_res_simplified:             0
% 19.46/3.00  inst_num_child_elim:                    0
% 19.46/3.00  inst_num_of_dismatching_blockings:      11214
% 19.46/3.00  inst_num_of_non_proper_insts:           5314
% 19.46/3.00  inst_num_of_duplicates:                 0
% 19.46/3.00  inst_inst_num_from_inst_to_res:         0
% 19.46/3.00  inst_dismatching_checking_time:         0.
% 19.46/3.00  
% 19.46/3.00  ------ Resolution
% 19.46/3.00  
% 19.46/3.00  res_num_of_clauses:                     0
% 19.46/3.00  res_num_in_passive:                     0
% 19.46/3.00  res_num_in_active:                      0
% 19.46/3.00  res_num_of_loops:                       134
% 19.46/3.00  res_forward_subset_subsumed:            152
% 19.46/3.00  res_backward_subset_subsumed:           0
% 19.46/3.00  res_forward_subsumed:                   0
% 19.46/3.00  res_backward_subsumed:                  0
% 19.46/3.00  res_forward_subsumption_resolution:     2
% 19.46/3.00  res_backward_subsumption_resolution:    0
% 19.46/3.00  res_clause_to_clause_subsumption:       17444
% 19.46/3.00  res_orphan_elimination:                 0
% 19.46/3.00  res_tautology_del:                      44
% 19.46/3.00  res_num_eq_res_simplified:              0
% 19.46/3.00  res_num_sel_changes:                    0
% 19.46/3.00  res_moves_from_active_to_pass:          0
% 19.46/3.00  
% 19.46/3.00  ------ Superposition
% 19.46/3.00  
% 19.46/3.00  sup_time_total:                         0.
% 19.46/3.00  sup_time_generating:                    0.
% 19.46/3.00  sup_time_sim_full:                      0.
% 19.46/3.00  sup_time_sim_immed:                     0.
% 19.46/3.00  
% 19.46/3.00  sup_num_of_clauses:                     2552
% 19.46/3.00  sup_num_in_active:                      367
% 19.46/3.00  sup_num_in_passive:                     2185
% 19.46/3.00  sup_num_of_loops:                       449
% 19.46/3.00  sup_fw_superposition:                   2644
% 19.46/3.00  sup_bw_superposition:                   2020
% 19.46/3.00  sup_immediate_simplified:               1638
% 19.46/3.00  sup_given_eliminated:                   0
% 19.46/3.00  comparisons_done:                       0
% 19.46/3.00  comparisons_avoided:                    0
% 19.46/3.00  
% 19.46/3.00  ------ Simplifications
% 19.46/3.00  
% 19.46/3.00  
% 19.46/3.00  sim_fw_subset_subsumed:                 176
% 19.46/3.00  sim_bw_subset_subsumed:                 124
% 19.46/3.00  sim_fw_subsumed:                        243
% 19.46/3.00  sim_bw_subsumed:                        2
% 19.46/3.00  sim_fw_subsumption_res:                 0
% 19.46/3.00  sim_bw_subsumption_res:                 0
% 19.46/3.00  sim_tautology_del:                      91
% 19.46/3.00  sim_eq_tautology_del:                   387
% 19.46/3.00  sim_eq_res_simp:                        0
% 19.46/3.00  sim_fw_demodulated:                     320
% 19.46/3.00  sim_bw_demodulated:                     80
% 19.46/3.00  sim_light_normalised:                   1137
% 19.46/3.00  sim_joinable_taut:                      0
% 19.46/3.00  sim_joinable_simp:                      0
% 19.46/3.00  sim_ac_normalised:                      0
% 19.46/3.00  sim_smt_subsumption:                    0
% 19.46/3.00  
%------------------------------------------------------------------------------
