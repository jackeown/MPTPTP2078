%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:07 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  172 (1520 expanded)
%              Number of clauses        :  121 ( 331 expanded)
%              Number of leaves         :   11 ( 613 expanded)
%              Depth                    :   24
%              Number of atoms          :  921 (19847 expanded)
%              Number of equality atoms :  146 ( 284 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X1,X3) )
                         => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                            | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X4)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,sK4))
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK4)
        & m1_pre_topc(X1,X3)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X4)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X4))
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,X4)
            & m1_pre_topc(X1,sK3)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X4)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,X4))
                & ~ r1_tsep_1(X1,sK2)
                & m1_pre_topc(sK2,X4)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X4))
                    & ~ r1_tsep_1(sK1,X2)
                    & m1_pre_topc(X2,X4)
                    & m1_pre_topc(sK1,X3)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
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
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                        & ~ r1_tsep_1(X1,X2)
                        & m1_pre_topc(X2,X4)
                        & m1_pre_topc(X1,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f26,f25,f24,f23,f22])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
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
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
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
    inference(equality_resolution,[],[f29])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X3)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_526,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_527,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_529,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_24])).

cnf(c_530,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_1074,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_3729,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_43)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_10533,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3729])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1083,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1547,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1081,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1549,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_755,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_756,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_760,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_26])).

cnf(c_761,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_726,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_727,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_26])).

cnf(c_732,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_731])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_697,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_698,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_26])).

cnf(c_703,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_702])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_660,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_661,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | r1_tsep_1(X0,X1)
    | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_26])).

cnf(c_666,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_721,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_703,c_666])).

cnf(c_750,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_732,c_721])).

cnf(c_777,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_761,c_750])).

cnf(c_1068,plain,
    ( r1_tsep_1(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | u1_struct_0(k2_tsep_1(sK0,X0_43,X1_43)) = k3_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_777])).

cnf(c_1562,plain,
    ( u1_struct_0(k2_tsep_1(sK0,X0_43,X1_43)) = k3_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
    | r1_tsep_1(X0_43,X1_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_7087,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | r1_tsep_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1562])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8257,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | r1_tsep_1(sK1,X0_43) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7087,c_30])).

cnf(c_8258,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
    | r1_tsep_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_8257])).

cnf(c_8269,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_8258])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1979,plain,
    ( r1_tsep_1(sK1,X0_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_2282,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_8433,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8269,c_23,c_22,c_21,c_20,c_13,c_2282])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1087,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1543,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1085,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1545,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_7085,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | r1_tsep_1(sK3,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1562])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7560,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | r1_tsep_1(sK3,X0_43) = iProver_top
    | u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7085,c_34])).

cnf(c_7561,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
    | r1_tsep_1(sK3,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_7560])).

cnf(c_7570,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_tsep_1(sK3,sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_7561])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_36,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_37,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_40,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1969,plain,
    ( r1_tsep_1(sK3,X0_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_2244,plain,
    ( r1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_2245,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_tsep_1(sK3,sK4) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2244])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1089,negated_conjecture,
    ( m1_pre_topc(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1541,plain,
    ( m1_pre_topc(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_8,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_421,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_422,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_424,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_26,c_24])).

cnf(c_425,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_1077,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | r1_tsep_1(X2_43,X0_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ m1_pre_topc(X2_43,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43) ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_1553,plain,
    ( r1_tsep_1(X0_43,X1_43) != iProver_top
    | r1_tsep_1(X2_43,X0_43) = iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | m1_pre_topc(X2_43,sK0) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_4358,plain,
    ( r1_tsep_1(X0_43,sK4) != iProver_top
    | r1_tsep_1(sK2,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1553])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5077,plain,
    ( r1_tsep_1(X0_43,sK4) != iProver_top
    | r1_tsep_1(sK2,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4358,c_32,c_33,c_36,c_37])).

cnf(c_5088,plain,
    ( r1_tsep_1(sK3,sK4) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_5077])).

cnf(c_5131,plain,
    ( r1_tsep_1(sK2,sK3) = iProver_top
    | r1_tsep_1(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5088,c_34])).

cnf(c_5132,plain,
    ( r1_tsep_1(sK3,sK4) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5131])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1088,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1542,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_4359,plain,
    ( r1_tsep_1(X0_43,sK3) != iProver_top
    | r1_tsep_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1553])).

cnf(c_31,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5196,plain,
    ( r1_tsep_1(X0_43,sK3) != iProver_top
    | r1_tsep_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4359,c_30,c_31,c_34,c_35])).

cnf(c_5208,plain,
    ( r1_tsep_1(sK2,sK3) != iProver_top
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_5196])).

cnf(c_7650,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7570,c_32,c_34,c_35,c_36,c_37,c_40,c_2245,c_5088,c_5208])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1092,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X3_44)
    | r1_tarski(k3_xboole_0(X2_44,X0_44),k3_xboole_0(X3_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1538,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(X2_44,X3_44) != iProver_top
    | r1_tarski(k3_xboole_0(X2_44,X0_44),k3_xboole_0(X3_44,X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_7655,plain,
    ( r1_tarski(X0_44,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X1_44,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k3_xboole_0(X1_44,X0_44),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7650,c_1538])).

cnf(c_8563,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8433,c_7655])).

cnf(c_8591,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8563])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_546,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_547,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_551,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_24])).

cnf(c_552,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_1073,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_1879,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_2215,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_1874,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_2200,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_1069,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1_43,X0_43),sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_761])).

cnf(c_1814,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_43,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2057,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_1804,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_43,sK4),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2027,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_12,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10533,c_8591,c_2215,c_2200,c_2057,c_2027,c_12,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:11:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.76/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.99  
% 3.76/0.99  ------  iProver source info
% 3.76/0.99  
% 3.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.99  git: non_committed_changes: false
% 3.76/0.99  git: last_make_outside_of_git: false
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    --mode clausify
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         false
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     num_symb
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       true
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     false
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   []
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_full_bw                           [BwDemod]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  ------ Parsing...
% 3.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.99  ------ Proving...
% 3.76/0.99  ------ Problem Properties 
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  clauses                                 25
% 3.76/0.99  conjectures                             13
% 3.76/0.99  EPR                                     16
% 3.76/0.99  Horn                                    16
% 3.76/0.99  unary                                   13
% 3.76/0.99  binary                                  0
% 3.76/0.99  lits                                    91
% 3.76/0.99  lits eq                                 3
% 3.76/0.99  fd_pure                                 0
% 3.76/0.99  fd_pseudo                               0
% 3.76/0.99  fd_cond                                 0
% 3.76/0.99  fd_pseudo_cond                          1
% 3.76/0.99  AC symbols                              0
% 3.76/0.99  
% 3.76/0.99  ------ Schedule dynamic 5 is on 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  Current options:
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    --mode clausify
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         false
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     none
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       false
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     false
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   []
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_full_bw                           [BwDemod]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ Proving...
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS status Theorem for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  fof(f5,axiom,(
% 3.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f16,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f5])).
% 3.76/0.99  
% 3.76/0.99  fof(f17,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.76/0.99    inference(flattening,[],[f16])).
% 3.76/0.99  
% 3.76/0.99  fof(f21,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.76/0.99    inference(nnf_transformation,[],[f17])).
% 3.76/0.99  
% 3.76/0.99  fof(f38,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f21])).
% 3.76/0.99  
% 3.76/0.99  fof(f6,conjecture,(
% 3.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f7,negated_conjecture,(
% 3.76/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 3.76/0.99    inference(negated_conjecture,[],[f6])).
% 3.76/0.99  
% 3.76/0.99  fof(f18,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f7])).
% 3.76/0.99  
% 3.76/0.99  fof(f19,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/0.99    inference(flattening,[],[f18])).
% 3.76/0.99  
% 3.76/0.99  fof(f26,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,sK4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK4) & m1_pre_topc(X1,X3) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f25,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,sK3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f24,plain,(
% 3.76/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(sK2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f23,plain,(
% 3.76/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(sK1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f22,plain,(
% 3.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f27,plain,(
% 3.76/0.99    ((((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f26,f25,f24,f23,f22])).
% 3.76/0.99  
% 3.76/0.99  fof(f41,plain,(
% 3.76/0.99    v2_pre_topc(sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f42,plain,(
% 3.76/0.99    l1_pre_topc(sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f46,plain,(
% 3.76/0.99    m1_pre_topc(sK2,sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f44,plain,(
% 3.76/0.99    m1_pre_topc(sK1,sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f3,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f12,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f3])).
% 3.76/0.99  
% 3.76/0.99  fof(f13,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/0.99    inference(flattening,[],[f12])).
% 3.76/0.99  
% 3.76/0.99  fof(f33,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f40,plain,(
% 3.76/0.99    ~v2_struct_0(sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f32,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f31,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f2,axiom,(
% 3.76/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)))))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f10,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f2])).
% 3.76/0.99  
% 3.76/0.99  fof(f11,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/0.99    inference(flattening,[],[f10])).
% 3.76/0.99  
% 3.76/0.99  fof(f20,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/0.99    inference(nnf_transformation,[],[f11])).
% 3.76/0.99  
% 3.76/0.99  fof(f29,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f20])).
% 3.76/0.99  
% 3.76/0.99  fof(f55,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(equality_resolution,[],[f29])).
% 3.76/0.99  
% 3.76/0.99  fof(f43,plain,(
% 3.76/0.99    ~v2_struct_0(sK1)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f45,plain,(
% 3.76/0.99    ~v2_struct_0(sK2)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f53,plain,(
% 3.76/0.99    ~r1_tsep_1(sK1,sK2)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f50,plain,(
% 3.76/0.99    m1_pre_topc(sK4,sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f48,plain,(
% 3.76/0.99    m1_pre_topc(sK3,sK0)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f47,plain,(
% 3.76/0.99    ~v2_struct_0(sK3)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f49,plain,(
% 3.76/0.99    ~v2_struct_0(sK4)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f52,plain,(
% 3.76/0.99    m1_pre_topc(sK2,sK4)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f4,axiom,(
% 3.76/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f14,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/0.99    inference(ennf_transformation,[],[f4])).
% 3.76/0.99  
% 3.76/0.99  fof(f15,plain,(
% 3.76/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/0.99    inference(flattening,[],[f14])).
% 3.76/0.99  
% 3.76/0.99  fof(f35,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X3) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f15])).
% 3.76/0.99  
% 3.76/0.99  fof(f51,plain,(
% 3.76/0.99    m1_pre_topc(sK1,sK3)),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f1,axiom,(
% 3.76/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f8,plain,(
% 3.76/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f1])).
% 3.76/0.99  
% 3.76/0.99  fof(f9,plain,(
% 3.76/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 3.76/0.99    inference(flattening,[],[f8])).
% 3.76/0.99  
% 3.76/0.99  fof(f28,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f9])).
% 3.76/0.99  
% 3.76/0.99  fof(f39,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f21])).
% 3.76/0.99  
% 3.76/0.99  fof(f54,plain,(
% 3.76/0.99    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  cnf(c_11,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | m1_pre_topc(X2,X0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 3.76/0.99      | ~ v2_pre_topc(X1)
% 3.76/0.99      | ~ l1_pre_topc(X1) ),
% 3.76/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_25,negated_conjecture,
% 3.76/0.99      ( v2_pre_topc(sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_526,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | m1_pre_topc(X2,X0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 3.76/0.99      | ~ l1_pre_topc(X1)
% 3.76/0.99      | sK0 != X1 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_527,plain,
% 3.76/0.99      ( m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | ~ l1_pre_topc(sK0) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_24,negated_conjecture,
% 3.76/0.99      ( l1_pre_topc(sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_529,plain,
% 3.76/0.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | m1_pre_topc(X0,X1) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_527,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_530,plain,
% 3.76/0.99      ( m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_529]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1074,plain,
% 3.76/0.99      ( m1_pre_topc(X0_43,X1_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1_43,sK0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_530]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3729,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_43)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1074]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10533,plain,
% 3.76/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_3729]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_20,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1083,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1547,plain,
% 3.76/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_22,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK1,sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1081,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK1,sK0) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1549,plain,
% 3.76/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.76/0.99      | ~ l1_pre_topc(X1)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_755,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | sK0 != X1 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_756,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(sK0) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_755]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_26,negated_conjecture,
% 3.76/0.99      ( ~ v2_struct_0(sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_760,plain,
% 3.76/0.99      ( v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_756,c_26]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_761,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_760]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ l1_pre_topc(X1)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_726,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v1_pre_topc(k2_tsep_1(X1,X2,X0))
% 3.76/0.99      | sK0 != X1 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_727,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(sK0)
% 3.76/0.99      | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_731,plain,
% 3.76/0.99      ( v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_727,c_26]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_732,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v1_pre_topc(k2_tsep_1(sK0,X1,X0)) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_731]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ l1_pre_topc(X1)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_697,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
% 3.76/0.99      | sK0 != X1 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_698,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
% 3.76/0.99      | v2_struct_0(sK0) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_697]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_702,plain,
% 3.76/0.99      ( ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_698,c_26]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_703,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0)) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_702]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X1,X2)
% 3.76/0.99      | ~ m1_pre_topc(X0,X2)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 3.76/0.99      | ~ l1_pre_topc(X2)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_660,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X1,X2)
% 3.76/0.99      | ~ m1_pre_topc(X0,X2)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(X2,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | sK0 != X2 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_661,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | v2_struct_0(sK0)
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_660]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_665,plain,
% 3.76/0.99      ( v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_661,c_26]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_666,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_665]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_721,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | ~ v1_pre_topc(k2_tsep_1(sK0,X0,X1))
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(backward_subsumption_resolution,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_703,c_666]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_750,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(backward_subsumption_resolution,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_732,c_721]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_777,plain,
% 3.76/0.99      ( r1_tsep_1(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0,X1)) = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(backward_subsumption_resolution,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_761,c_750]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1068,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,X1_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1_43,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(X1_43)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,X0_43,X1_43)) = k3_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_777]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1562,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,X0_43,X1_43)) = k3_xboole_0(u1_struct_0(X0_43),u1_struct_0(X1_43))
% 3.76/0.99      | r1_tsep_1(X0_43,X1_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(X1_43) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7087,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 3.76/0.99      | r1_tsep_1(sK1,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1549,c_1562]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_23,negated_conjecture,
% 3.76/0.99      ( ~ v2_struct_0(sK1) ),
% 3.76/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_30,plain,
% 3.76/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8257,plain,
% 3.76/0.99      ( v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK1,X0_43) = iProver_top
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_7087,c_30]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8258,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43))
% 3.76/0.99      | r1_tsep_1(sK1,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_8257]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8269,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
% 3.76/0.99      | r1_tsep_1(sK1,sK2) = iProver_top
% 3.76/0.99      | v2_struct_0(sK2) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1547,c_8258]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_21,negated_conjecture,
% 3.76/0.99      ( ~ v2_struct_0(sK2) ),
% 3.76/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_13,negated_conjecture,
% 3.76/0.99      ( ~ r1_tsep_1(sK1,sK2) ),
% 3.76/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1979,plain,
% 3.76/0.99      ( r1_tsep_1(sK1,X0_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(sK1)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK1,X0_43)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2282,plain,
% 3.76/0.99      ( r1_tsep_1(sK1,sK2)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.76/0.99      | v2_struct_0(sK2)
% 3.76/0.99      | v2_struct_0(sK1)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1979]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8433,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_8269,c_23,c_22,c_21,c_20,c_13,c_2282]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_16,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK4,sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1087,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK4,sK0) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1543,plain,
% 3.76/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_18,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1085,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1545,plain,
% 3.76/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7085,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 3.76/0.99      | r1_tsep_1(sK3,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1545,c_1562]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_19,negated_conjecture,
% 3.76/0.99      ( ~ v2_struct_0(sK3) ),
% 3.76/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_34,plain,
% 3.76/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7560,plain,
% 3.76/0.99      ( v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK3,X0_43) = iProver_top
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_7085,c_34]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7561,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43))
% 3.76/0.99      | r1_tsep_1(sK3,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_7560]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7570,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.76/0.99      | r1_tsep_1(sK3,sK4) = iProver_top
% 3.76/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1543,c_7561]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_32,plain,
% 3.76/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_35,plain,
% 3.76/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_17,negated_conjecture,
% 3.76/0.99      ( ~ v2_struct_0(sK4) ),
% 3.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_36,plain,
% 3.76/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_37,plain,
% 3.76/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_40,plain,
% 3.76/0.99      ( r1_tsep_1(sK1,sK2) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1969,plain,
% 3.76/0.99      ( r1_tsep_1(sK3,X0_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(sK3)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK3,X0_43)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2244,plain,
% 3.76/0.99      ( r1_tsep_1(sK3,sK4)
% 3.76/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.76/0.99      | v2_struct_0(sK4)
% 3.76/0.99      | v2_struct_0(sK3)
% 3.76/0.99      | u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1969]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2245,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.76/0.99      | r1_tsep_1(sK3,sK4) = iProver_top
% 3.76/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(sK4) = iProver_top
% 3.76/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2244]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_14,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK2,sK4) ),
% 3.76/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1089,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK2,sK4) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1541,plain,
% 3.76/0.99      ( m1_pre_topc(sK2,sK4) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8,plain,
% 3.76/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.76/0.99      | r1_tsep_1(X2,X0)
% 3.76/0.99      | ~ m1_pre_topc(X0,X3)
% 3.76/0.99      | ~ m1_pre_topc(X1,X3)
% 3.76/0.99      | ~ m1_pre_topc(X2,X3)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ v2_pre_topc(X3)
% 3.76/0.99      | ~ l1_pre_topc(X3)
% 3.76/0.99      | v2_struct_0(X3)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_421,plain,
% 3.76/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.76/0.99      | r1_tsep_1(X2,X0)
% 3.76/0.99      | ~ m1_pre_topc(X2,X3)
% 3.76/0.99      | ~ m1_pre_topc(X1,X3)
% 3.76/0.99      | ~ m1_pre_topc(X0,X3)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ l1_pre_topc(X3)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X3)
% 3.76/0.99      | sK0 != X3 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_422,plain,
% 3.76/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.76/0.99      | r1_tsep_1(X2,X0)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.76/0.99      | ~ l1_pre_topc(sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(sK0) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_424,plain,
% 3.76/0.99      ( v2_struct_0(X1)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | ~ r1_tsep_1(X0,X1)
% 3.76/0.99      | r1_tsep_1(X2,X0)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X2,sK0) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_422,c_26,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_425,plain,
% 3.76/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.76/0.99      | r1_tsep_1(X2,X0)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.76/0.99      | v2_struct_0(X0)
% 3.76/0.99      | v2_struct_0(X2)
% 3.76/0.99      | v2_struct_0(X1) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_424]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1077,plain,
% 3.76/0.99      ( ~ r1_tsep_1(X0_43,X1_43)
% 3.76/0.99      | r1_tsep_1(X2_43,X0_43)
% 3.76/0.99      | ~ m1_pre_topc(X2_43,X1_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X2_43,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(X1_43)
% 3.76/0.99      | v2_struct_0(X2_43) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_425]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1553,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,X1_43) != iProver_top
% 3.76/0.99      | r1_tsep_1(X2_43,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(X1_43,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(X2_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X2_43) = iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(X1_43) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4358,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,sK4) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK2,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(sK4) = iProver_top
% 3.76/0.99      | v2_struct_0(sK2) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1541,c_1553]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_33,plain,
% 3.76/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5077,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,sK4) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK2,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_4358,c_32,c_33,c_36,c_37]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5088,plain,
% 3.76/0.99      ( r1_tsep_1(sK3,sK4) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK2,sK3) = iProver_top
% 3.76/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1545,c_5077]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5131,plain,
% 3.76/0.99      ( r1_tsep_1(sK2,sK3) = iProver_top
% 3.76/0.99      | r1_tsep_1(sK3,sK4) != iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_5088,c_34]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5132,plain,
% 3.76/0.99      ( r1_tsep_1(sK3,sK4) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK2,sK3) = iProver_top ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_5131]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_15,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK1,sK3) ),
% 3.76/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1088,negated_conjecture,
% 3.76/0.99      ( m1_pre_topc(sK1,sK3) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1542,plain,
% 3.76/0.99      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4359,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,sK3) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK1,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.76/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top
% 3.76/0.99      | v2_struct_0(sK3) = iProver_top
% 3.76/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1542,c_1553]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_31,plain,
% 3.76/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5196,plain,
% 3.76/0.99      ( r1_tsep_1(X0_43,sK3) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK1,X0_43) = iProver_top
% 3.76/0.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 3.76/0.99      | v2_struct_0(X0_43) = iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_4359,c_30,c_31,c_34,c_35]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5208,plain,
% 3.76/0.99      ( r1_tsep_1(sK2,sK3) != iProver_top
% 3.76/0.99      | r1_tsep_1(sK1,sK2) = iProver_top
% 3.76/0.99      | v2_struct_0(sK2) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1547,c_5196]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7650,plain,
% 3.76/0.99      ( u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_7570,c_32,c_34,c_35,c_36,c_37,c_40,c_2245,c_5088,
% 3.76/0.99                 c_5208]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_0,plain,
% 3.76/0.99      ( ~ r1_tarski(X0,X1)
% 3.76/0.99      | ~ r1_tarski(X2,X3)
% 3.76/0.99      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1092,plain,
% 3.76/0.99      ( ~ r1_tarski(X0_44,X1_44)
% 3.76/0.99      | ~ r1_tarski(X2_44,X3_44)
% 3.76/0.99      | r1_tarski(k3_xboole_0(X2_44,X0_44),k3_xboole_0(X3_44,X1_44)) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1538,plain,
% 3.76/0.99      ( r1_tarski(X0_44,X1_44) != iProver_top
% 3.76/0.99      | r1_tarski(X2_44,X3_44) != iProver_top
% 3.76/0.99      | r1_tarski(k3_xboole_0(X2_44,X0_44),k3_xboole_0(X3_44,X1_44)) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7655,plain,
% 3.76/0.99      ( r1_tarski(X0_44,u1_struct_0(sK4)) != iProver_top
% 3.76/0.99      | r1_tarski(X1_44,u1_struct_0(sK3)) != iProver_top
% 3.76/0.99      | r1_tarski(k3_xboole_0(X1_44,X0_44),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_7650,c_1538]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8563,plain,
% 3.76/0.99      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) = iProver_top
% 3.76/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) != iProver_top
% 3.76/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_8433,c_7655]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8591,plain,
% 3.76/0.99      ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
% 3.76/0.99      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 3.76/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8563]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X1)
% 3.76/0.99      | ~ m1_pre_topc(X2,X0)
% 3.76/0.99      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 3.76/0.99      | ~ v2_pre_topc(X1)
% 3.76/0.99      | ~ l1_pre_topc(X1) ),
% 3.76/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_546,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X1,X2)
% 3.76/0.99      | ~ m1_pre_topc(X0,X2)
% 3.76/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | ~ l1_pre_topc(X2)
% 3.76/0.99      | sK0 != X2 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_547,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | ~ l1_pre_topc(sK0) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_551,plain,
% 3.76/0.99      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X0,X1) ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_547,c_24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_552,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.76/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_551]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1073,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 3.76/0.99      | ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1_43,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(X0_43),u1_struct_0(X1_43)) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_552]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1879,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK1,X0_43)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1073]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2215,plain,
% 3.76/0.99      ( ~ m1_pre_topc(sK3,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK3)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1879]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1874,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK2,X0_43)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_43)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1073]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2200,plain,
% 3.76/0.99      ( ~ m1_pre_topc(sK4,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK4)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.76/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1874]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1069,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | ~ m1_pre_topc(X1_43,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X1_43,X0_43),sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(X1_43) ),
% 3.76/0.99      inference(subtyping,[status(esa)],[c_761]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1814,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0_43,sK2),sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(sK2) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2057,plain,
% 3.76/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.76/0.99      | v2_struct_0(sK2)
% 3.76/0.99      | v2_struct_0(sK1) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1814]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1804,plain,
% 3.76/0.99      ( ~ m1_pre_topc(X0_43,sK0)
% 3.76/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0_43,sK4),sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.76/0.99      | v2_struct_0(X0_43)
% 3.76/0.99      | v2_struct_0(sK4) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2027,plain,
% 3.76/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.76/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.76/0.99      | v2_struct_0(sK4)
% 3.76/0.99      | v2_struct_0(sK3) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_12,negated_conjecture,
% 3.76/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(contradiction,plain,
% 3.76/0.99      ( $false ),
% 3.76/0.99      inference(minisat,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_10533,c_8591,c_2215,c_2200,c_2057,c_2027,c_12,c_14,
% 3.76/0.99                 c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23]) ).
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  ------                               Statistics
% 3.76/0.99  
% 3.76/0.99  ------ General
% 3.76/0.99  
% 3.76/0.99  abstr_ref_over_cycles:                  0
% 3.76/0.99  abstr_ref_under_cycles:                 0
% 3.76/0.99  gc_basic_clause_elim:                   0
% 3.76/0.99  forced_gc_time:                         0
% 3.76/0.99  parsing_time:                           0.018
% 3.76/0.99  unif_index_cands_time:                  0.
% 3.76/0.99  unif_index_add_time:                    0.
% 3.76/0.99  orderings_time:                         0.
% 3.76/0.99  out_proof_time:                         0.015
% 3.76/0.99  total_time:                             0.38
% 3.76/0.99  num_of_symbols:                         48
% 3.76/0.99  num_of_terms:                           11327
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing
% 3.76/0.99  
% 3.76/0.99  num_of_splits:                          0
% 3.76/0.99  num_of_split_atoms:                     0
% 3.76/0.99  num_of_reused_defs:                     0
% 3.76/0.99  num_eq_ax_congr_red:                    0
% 3.76/0.99  num_of_sem_filtered_clauses:            1
% 3.76/0.99  num_of_subtypes:                        2
% 3.76/0.99  monotx_restored_types:                  0
% 3.76/0.99  sat_num_of_epr_types:                   0
% 3.76/0.99  sat_num_of_non_cyclic_types:            0
% 3.76/0.99  sat_guarded_non_collapsed_types:        1
% 3.76/0.99  num_pure_diseq_elim:                    0
% 3.76/0.99  simp_replaced_by:                       0
% 3.76/0.99  res_preprocessed:                       127
% 3.76/0.99  prep_upred:                             0
% 3.76/0.99  prep_unflattend:                        14
% 3.76/0.99  smt_new_axioms:                         0
% 3.76/0.99  pred_elim_cands:                        5
% 3.76/0.99  pred_elim:                              2
% 3.76/0.99  pred_elim_cl:                           2
% 3.76/0.99  pred_elim_cycles:                       5
% 3.76/0.99  merged_defs:                            0
% 3.76/0.99  merged_defs_ncl:                        0
% 3.76/0.99  bin_hyper_res:                          0
% 3.76/0.99  prep_cycles:                            4
% 3.76/0.99  pred_elim_time:                         0.012
% 3.76/0.99  splitting_time:                         0.
% 3.76/0.99  sem_filter_time:                        0.
% 3.76/0.99  monotx_time:                            0.
% 3.76/0.99  subtype_inf_time:                       0.
% 3.76/0.99  
% 3.76/0.99  ------ Problem properties
% 3.76/0.99  
% 3.76/0.99  clauses:                                25
% 3.76/0.99  conjectures:                            13
% 3.76/0.99  epr:                                    16
% 3.76/0.99  horn:                                   16
% 3.76/0.99  ground:                                 13
% 3.76/0.99  unary:                                  13
% 3.76/0.99  binary:                                 0
% 3.76/0.99  lits:                                   91
% 3.76/0.99  lits_eq:                                3
% 3.76/0.99  fd_pure:                                0
% 3.76/0.99  fd_pseudo:                              0
% 3.76/0.99  fd_cond:                                0
% 3.76/0.99  fd_pseudo_cond:                         1
% 3.76/0.99  ac_symbols:                             0
% 3.76/0.99  
% 3.76/0.99  ------ Propositional Solver
% 3.76/0.99  
% 3.76/0.99  prop_solver_calls:                      27
% 3.76/0.99  prop_fast_solver_calls:                 1931
% 3.76/0.99  smt_solver_calls:                       0
% 3.76/0.99  smt_fast_solver_calls:                  0
% 3.76/0.99  prop_num_of_clauses:                    3232
% 3.76/0.99  prop_preprocess_simplified:             7910
% 3.76/0.99  prop_fo_subsumed:                       152
% 3.76/0.99  prop_solver_time:                       0.
% 3.76/0.99  smt_solver_time:                        0.
% 3.76/0.99  smt_fast_solver_time:                   0.
% 3.76/0.99  prop_fast_solver_time:                  0.
% 3.76/0.99  prop_unsat_core_time:                   0.
% 3.76/0.99  
% 3.76/0.99  ------ QBF
% 3.76/0.99  
% 3.76/0.99  qbf_q_res:                              0
% 3.76/0.99  qbf_num_tautologies:                    0
% 3.76/0.99  qbf_prep_cycles:                        0
% 3.76/0.99  
% 3.76/0.99  ------ BMC1
% 3.76/0.99  
% 3.76/0.99  bmc1_current_bound:                     -1
% 3.76/0.99  bmc1_last_solved_bound:                 -1
% 3.76/0.99  bmc1_unsat_core_size:                   -1
% 3.76/0.99  bmc1_unsat_core_parents_size:           -1
% 3.76/0.99  bmc1_merge_next_fun:                    0
% 3.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation
% 3.76/0.99  
% 3.76/0.99  inst_num_of_clauses:                    931
% 3.76/0.99  inst_num_in_passive:                    121
% 3.76/0.99  inst_num_in_active:                     554
% 3.76/0.99  inst_num_in_unprocessed:                255
% 3.76/0.99  inst_num_of_loops:                      587
% 3.76/0.99  inst_num_of_learning_restarts:          0
% 3.76/0.99  inst_num_moves_active_passive:          32
% 3.76/0.99  inst_lit_activity:                      0
% 3.76/0.99  inst_lit_activity_moves:                1
% 3.76/0.99  inst_num_tautologies:                   0
% 3.76/0.99  inst_num_prop_implied:                  0
% 3.76/0.99  inst_num_existing_simplified:           0
% 3.76/0.99  inst_num_eq_res_simplified:             0
% 3.76/0.99  inst_num_child_elim:                    0
% 3.76/0.99  inst_num_of_dismatching_blockings:      1726
% 3.76/0.99  inst_num_of_non_proper_insts:           836
% 3.76/0.99  inst_num_of_duplicates:                 0
% 3.76/0.99  inst_inst_num_from_inst_to_res:         0
% 3.76/0.99  inst_dismatching_checking_time:         0.
% 3.76/0.99  
% 3.76/0.99  ------ Resolution
% 3.76/0.99  
% 3.76/0.99  res_num_of_clauses:                     0
% 3.76/0.99  res_num_in_passive:                     0
% 3.76/0.99  res_num_in_active:                      0
% 3.76/0.99  res_num_of_loops:                       131
% 3.76/0.99  res_forward_subset_subsumed:            14
% 3.76/0.99  res_backward_subset_subsumed:           0
% 3.76/0.99  res_forward_subsumed:                   0
% 3.76/0.99  res_backward_subsumed:                  0
% 3.76/0.99  res_forward_subsumption_resolution:     5
% 3.76/0.99  res_backward_subsumption_resolution:    3
% 3.76/0.99  res_clause_to_clause_subsumption:       922
% 3.76/0.99  res_orphan_elimination:                 0
% 3.76/0.99  res_tautology_del:                      39
% 3.76/0.99  res_num_eq_res_simplified:              0
% 3.76/0.99  res_num_sel_changes:                    0
% 3.76/0.99  res_moves_from_active_to_pass:          0
% 3.76/0.99  
% 3.76/0.99  ------ Superposition
% 3.76/0.99  
% 3.76/0.99  sup_time_total:                         0.
% 3.76/0.99  sup_time_generating:                    0.
% 3.76/0.99  sup_time_sim_full:                      0.
% 3.76/0.99  sup_time_sim_immed:                     0.
% 3.76/0.99  
% 3.76/0.99  sup_num_of_clauses:                     190
% 3.76/0.99  sup_num_in_active:                      112
% 3.76/0.99  sup_num_in_passive:                     78
% 3.76/0.99  sup_num_of_loops:                       116
% 3.76/0.99  sup_fw_superposition:                   172
% 3.76/0.99  sup_bw_superposition:                   59
% 3.76/0.99  sup_immediate_simplified:               5
% 3.76/0.99  sup_given_eliminated:                   0
% 3.76/0.99  comparisons_done:                       0
% 3.76/0.99  comparisons_avoided:                    0
% 3.76/0.99  
% 3.76/0.99  ------ Simplifications
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  sim_fw_subset_subsumed:                 5
% 3.76/0.99  sim_bw_subset_subsumed:                 4
% 3.76/0.99  sim_fw_subsumed:                        0
% 3.76/0.99  sim_bw_subsumed:                        0
% 3.76/0.99  sim_fw_subsumption_res:                 6
% 3.76/0.99  sim_bw_subsumption_res:                 0
% 3.76/0.99  sim_tautology_del:                      1
% 3.76/0.99  sim_eq_tautology_del:                   0
% 3.76/0.99  sim_eq_res_simp:                        0
% 3.76/0.99  sim_fw_demodulated:                     0
% 3.76/0.99  sim_bw_demodulated:                     0
% 3.76/0.99  sim_light_normalised:                   0
% 3.76/0.99  sim_joinable_taut:                      0
% 3.76/0.99  sim_joinable_simp:                      0
% 3.76/0.99  sim_ac_normalised:                      0
% 3.76/0.99  sim_smt_subsumption:                    0
% 3.76/0.99  
%------------------------------------------------------------------------------
