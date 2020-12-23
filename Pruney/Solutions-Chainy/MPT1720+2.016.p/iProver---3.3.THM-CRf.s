%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:10 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 467 expanded)
%              Number of clauses        :   79 ( 118 expanded)
%              Number of leaves         :    9 ( 158 expanded)
%              Depth                    :   25
%              Number of atoms          :  585 (4576 expanded)
%              Number of equality atoms :   94 ( 120 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,
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

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22,f21,f20,f19])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(equality_resolution,[],[f25])).

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_726,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1067,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_722,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1071,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

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
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_112,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_5,c_4,c_3])).

cnf(c_113,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_112])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_322,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_113,c_17])).

cnf(c_323,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_327,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_19])).

cnf(c_328,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_717,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | v2_struct_0(X1_41)
    | v2_struct_0(X0_41)
    | u1_struct_0(k1_tsep_1(sK0,X0_41,X1_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_1076,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0_41,X1_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X1_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(X1_41,sK0) != iProver_top
    | v2_struct_0(X1_41) = iProver_top
    | v2_struct_0(X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2782,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1076])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3678,plain,
    ( v2_struct_0(X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2782,c_23])).

cnf(c_3679,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41))
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | v2_struct_0(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_3678])).

cnf(c_3687,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_3679])).

cnf(c_12,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1304,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_41)
    | v2_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1570,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_3928,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3687,c_16,c_15,c_12,c_11,c_1570])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_730,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X1_42)
    | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1063,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X1_42) != iProver_top
    | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_3932,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),X0_42) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0_42) != iProver_top
    | r1_tarski(u1_struct_0(sK1),X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_3928,c_1063])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_213,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_215,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_17])).

cnf(c_216,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_719,plain,
    ( m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_1074,plain,
    ( m1_pre_topc(X0_41,X1_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(X1_41,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_4933,plain,
    ( m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3932,c_1074])).

cnf(c_24,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_28,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_397,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_398,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_402,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_19])).

cnf(c_403,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_714,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_41,X1_41),sK0)
    | v2_struct_0(X1_41)
    | v2_struct_0(X0_41) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_1235,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_41),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_41)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1422,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_1423,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_19645,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
    | m1_pre_topc(X0_41,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4933,c_23,c_24,c_27,c_28,c_1423])).

cnf(c_19646,plain,
    ( m1_pre_topc(X0_41,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19645])).

cnf(c_8,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_729,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1064,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_19655,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19646,c_1064])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_232,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_233,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_237,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_17])).

cnf(c_238,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_237])).

cnf(c_718,plain,
    ( ~ m1_pre_topc(X0_41,X1_41)
    | ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(X1_41,sK0)
    | r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_1280,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(sK1,X0_41)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1528,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1529,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_1270,plain,
    ( ~ m1_pre_topc(X0_41,sK0)
    | ~ m1_pre_topc(sK3,X0_41)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1510,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1511,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_9,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_30,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19655,c_1529,c_1511,c_30,c_29,c_28,c_26,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:46:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.54/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/1.53  
% 7.54/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.53  
% 7.54/1.53  ------  iProver source info
% 7.54/1.53  
% 7.54/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.53  git: non_committed_changes: false
% 7.54/1.53  git: last_make_outside_of_git: false
% 7.54/1.53  
% 7.54/1.53  ------ 
% 7.54/1.53  
% 7.54/1.53  ------ Input Options
% 7.54/1.53  
% 7.54/1.53  --out_options                           all
% 7.54/1.53  --tptp_safe_out                         true
% 7.54/1.53  --problem_path                          ""
% 7.54/1.53  --include_path                          ""
% 7.54/1.53  --clausifier                            res/vclausify_rel
% 7.54/1.53  --clausifier_options                    --mode clausify
% 7.54/1.53  --stdin                                 false
% 7.54/1.53  --stats_out                             all
% 7.54/1.53  
% 7.54/1.53  ------ General Options
% 7.54/1.53  
% 7.54/1.53  --fof                                   false
% 7.54/1.53  --time_out_real                         305.
% 7.54/1.53  --time_out_virtual                      -1.
% 7.54/1.53  --symbol_type_check                     false
% 7.54/1.53  --clausify_out                          false
% 7.54/1.53  --sig_cnt_out                           false
% 7.54/1.53  --trig_cnt_out                          false
% 7.54/1.53  --trig_cnt_out_tolerance                1.
% 7.54/1.53  --trig_cnt_out_sk_spl                   false
% 7.54/1.53  --abstr_cl_out                          false
% 7.54/1.53  
% 7.54/1.53  ------ Global Options
% 7.54/1.53  
% 7.54/1.53  --schedule                              default
% 7.54/1.53  --add_important_lit                     false
% 7.54/1.53  --prop_solver_per_cl                    1000
% 7.54/1.53  --min_unsat_core                        false
% 7.54/1.53  --soft_assumptions                      false
% 7.54/1.53  --soft_lemma_size                       3
% 7.54/1.53  --prop_impl_unit_size                   0
% 7.54/1.53  --prop_impl_unit                        []
% 7.54/1.53  --share_sel_clauses                     true
% 7.54/1.53  --reset_solvers                         false
% 7.54/1.53  --bc_imp_inh                            [conj_cone]
% 7.54/1.53  --conj_cone_tolerance                   3.
% 7.54/1.53  --extra_neg_conj                        none
% 7.54/1.53  --large_theory_mode                     true
% 7.54/1.53  --prolific_symb_bound                   200
% 7.54/1.53  --lt_threshold                          2000
% 7.54/1.53  --clause_weak_htbl                      true
% 7.54/1.53  --gc_record_bc_elim                     false
% 7.54/1.53  
% 7.54/1.53  ------ Preprocessing Options
% 7.54/1.53  
% 7.54/1.53  --preprocessing_flag                    true
% 7.54/1.53  --time_out_prep_mult                    0.1
% 7.54/1.53  --splitting_mode                        input
% 7.54/1.53  --splitting_grd                         true
% 7.54/1.53  --splitting_cvd                         false
% 7.54/1.53  --splitting_cvd_svl                     false
% 7.54/1.53  --splitting_nvd                         32
% 7.54/1.53  --sub_typing                            true
% 7.54/1.53  --prep_gs_sim                           true
% 7.54/1.53  --prep_unflatten                        true
% 7.54/1.53  --prep_res_sim                          true
% 7.54/1.53  --prep_upred                            true
% 7.54/1.53  --prep_sem_filter                       exhaustive
% 7.54/1.53  --prep_sem_filter_out                   false
% 7.54/1.53  --pred_elim                             true
% 7.54/1.53  --res_sim_input                         true
% 7.54/1.53  --eq_ax_congr_red                       true
% 7.54/1.53  --pure_diseq_elim                       true
% 7.54/1.53  --brand_transform                       false
% 7.54/1.53  --non_eq_to_eq                          false
% 7.54/1.53  --prep_def_merge                        true
% 7.54/1.53  --prep_def_merge_prop_impl              false
% 7.54/1.53  --prep_def_merge_mbd                    true
% 7.54/1.53  --prep_def_merge_tr_red                 false
% 7.54/1.53  --prep_def_merge_tr_cl                  false
% 7.54/1.53  --smt_preprocessing                     true
% 7.54/1.53  --smt_ac_axioms                         fast
% 7.54/1.53  --preprocessed_out                      false
% 7.54/1.53  --preprocessed_stats                    false
% 7.54/1.53  
% 7.54/1.53  ------ Abstraction refinement Options
% 7.54/1.53  
% 7.54/1.53  --abstr_ref                             []
% 7.54/1.53  --abstr_ref_prep                        false
% 7.54/1.53  --abstr_ref_until_sat                   false
% 7.54/1.53  --abstr_ref_sig_restrict                funpre
% 7.54/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.53  --abstr_ref_under                       []
% 7.54/1.53  
% 7.54/1.53  ------ SAT Options
% 7.54/1.53  
% 7.54/1.53  --sat_mode                              false
% 7.54/1.53  --sat_fm_restart_options                ""
% 7.54/1.53  --sat_gr_def                            false
% 7.54/1.53  --sat_epr_types                         true
% 7.54/1.53  --sat_non_cyclic_types                  false
% 7.54/1.53  --sat_finite_models                     false
% 7.54/1.53  --sat_fm_lemmas                         false
% 7.54/1.53  --sat_fm_prep                           false
% 7.54/1.53  --sat_fm_uc_incr                        true
% 7.54/1.53  --sat_out_model                         small
% 7.54/1.53  --sat_out_clauses                       false
% 7.54/1.53  
% 7.54/1.53  ------ QBF Options
% 7.54/1.53  
% 7.54/1.53  --qbf_mode                              false
% 7.54/1.53  --qbf_elim_univ                         false
% 7.54/1.53  --qbf_dom_inst                          none
% 7.54/1.53  --qbf_dom_pre_inst                      false
% 7.54/1.53  --qbf_sk_in                             false
% 7.54/1.53  --qbf_pred_elim                         true
% 7.54/1.53  --qbf_split                             512
% 7.54/1.53  
% 7.54/1.53  ------ BMC1 Options
% 7.54/1.53  
% 7.54/1.53  --bmc1_incremental                      false
% 7.54/1.53  --bmc1_axioms                           reachable_all
% 7.54/1.53  --bmc1_min_bound                        0
% 7.54/1.53  --bmc1_max_bound                        -1
% 7.54/1.53  --bmc1_max_bound_default                -1
% 7.54/1.53  --bmc1_symbol_reachability              true
% 7.54/1.53  --bmc1_property_lemmas                  false
% 7.54/1.53  --bmc1_k_induction                      false
% 7.54/1.53  --bmc1_non_equiv_states                 false
% 7.54/1.53  --bmc1_deadlock                         false
% 7.54/1.53  --bmc1_ucm                              false
% 7.54/1.53  --bmc1_add_unsat_core                   none
% 7.54/1.53  --bmc1_unsat_core_children              false
% 7.54/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.53  --bmc1_out_stat                         full
% 7.54/1.53  --bmc1_ground_init                      false
% 7.54/1.53  --bmc1_pre_inst_next_state              false
% 7.54/1.53  --bmc1_pre_inst_state                   false
% 7.54/1.53  --bmc1_pre_inst_reach_state             false
% 7.54/1.53  --bmc1_out_unsat_core                   false
% 7.54/1.53  --bmc1_aig_witness_out                  false
% 7.54/1.53  --bmc1_verbose                          false
% 7.54/1.53  --bmc1_dump_clauses_tptp                false
% 7.54/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.53  --bmc1_dump_file                        -
% 7.54/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.53  --bmc1_ucm_extend_mode                  1
% 7.54/1.53  --bmc1_ucm_init_mode                    2
% 7.54/1.53  --bmc1_ucm_cone_mode                    none
% 7.54/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.53  --bmc1_ucm_relax_model                  4
% 7.54/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.53  --bmc1_ucm_layered_model                none
% 7.54/1.53  --bmc1_ucm_max_lemma_size               10
% 7.54/1.53  
% 7.54/1.53  ------ AIG Options
% 7.54/1.53  
% 7.54/1.53  --aig_mode                              false
% 7.54/1.53  
% 7.54/1.53  ------ Instantiation Options
% 7.54/1.53  
% 7.54/1.53  --instantiation_flag                    true
% 7.54/1.53  --inst_sos_flag                         false
% 7.54/1.53  --inst_sos_phase                        true
% 7.54/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.53  --inst_lit_sel_side                     num_symb
% 7.54/1.53  --inst_solver_per_active                1400
% 7.54/1.53  --inst_solver_calls_frac                1.
% 7.54/1.53  --inst_passive_queue_type               priority_queues
% 7.54/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.53  --inst_passive_queues_freq              [25;2]
% 7.54/1.53  --inst_dismatching                      true
% 7.54/1.53  --inst_eager_unprocessed_to_passive     true
% 7.54/1.53  --inst_prop_sim_given                   true
% 7.54/1.53  --inst_prop_sim_new                     false
% 7.54/1.53  --inst_subs_new                         false
% 7.54/1.53  --inst_eq_res_simp                      false
% 7.54/1.53  --inst_subs_given                       false
% 7.54/1.53  --inst_orphan_elimination               true
% 7.54/1.53  --inst_learning_loop_flag               true
% 7.54/1.53  --inst_learning_start                   3000
% 7.54/1.53  --inst_learning_factor                  2
% 7.54/1.53  --inst_start_prop_sim_after_learn       3
% 7.54/1.53  --inst_sel_renew                        solver
% 7.54/1.53  --inst_lit_activity_flag                true
% 7.54/1.53  --inst_restr_to_given                   false
% 7.54/1.53  --inst_activity_threshold               500
% 7.54/1.53  --inst_out_proof                        true
% 7.54/1.53  
% 7.54/1.53  ------ Resolution Options
% 7.54/1.53  
% 7.54/1.53  --resolution_flag                       true
% 7.54/1.53  --res_lit_sel                           adaptive
% 7.54/1.53  --res_lit_sel_side                      none
% 7.54/1.53  --res_ordering                          kbo
% 7.54/1.53  --res_to_prop_solver                    active
% 7.54/1.53  --res_prop_simpl_new                    false
% 7.54/1.53  --res_prop_simpl_given                  true
% 7.54/1.53  --res_passive_queue_type                priority_queues
% 7.54/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.53  --res_passive_queues_freq               [15;5]
% 7.54/1.53  --res_forward_subs                      full
% 7.54/1.53  --res_backward_subs                     full
% 7.54/1.53  --res_forward_subs_resolution           true
% 7.54/1.53  --res_backward_subs_resolution          true
% 7.54/1.53  --res_orphan_elimination                true
% 7.54/1.53  --res_time_limit                        2.
% 7.54/1.53  --res_out_proof                         true
% 7.54/1.53  
% 7.54/1.53  ------ Superposition Options
% 7.54/1.53  
% 7.54/1.53  --superposition_flag                    true
% 7.54/1.53  --sup_passive_queue_type                priority_queues
% 7.54/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.53  --demod_completeness_check              fast
% 7.54/1.53  --demod_use_ground                      true
% 7.54/1.53  --sup_to_prop_solver                    passive
% 7.54/1.53  --sup_prop_simpl_new                    true
% 7.54/1.53  --sup_prop_simpl_given                  true
% 7.54/1.53  --sup_fun_splitting                     false
% 7.54/1.53  --sup_smt_interval                      50000
% 7.54/1.53  
% 7.54/1.53  ------ Superposition Simplification Setup
% 7.54/1.53  
% 7.54/1.53  --sup_indices_passive                   []
% 7.54/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_full_bw                           [BwDemod]
% 7.54/1.53  --sup_immed_triv                        [TrivRules]
% 7.54/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_immed_bw_main                     []
% 7.54/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.53  
% 7.54/1.53  ------ Combination Options
% 7.54/1.53  
% 7.54/1.53  --comb_res_mult                         3
% 7.54/1.53  --comb_sup_mult                         2
% 7.54/1.53  --comb_inst_mult                        10
% 7.54/1.53  
% 7.54/1.53  ------ Debug Options
% 7.54/1.53  
% 7.54/1.53  --dbg_backtrace                         false
% 7.54/1.53  --dbg_dump_prop_clauses                 false
% 7.54/1.53  --dbg_dump_prop_clauses_file            -
% 7.54/1.53  --dbg_out_stat                          false
% 7.54/1.53  ------ Parsing...
% 7.54/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.53  
% 7.54/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.54/1.53  
% 7.54/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.53  
% 7.54/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.53  ------ Proving...
% 7.54/1.53  ------ Problem Properties 
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  clauses                                 18
% 7.54/1.53  conjectures                             10
% 7.54/1.53  EPR                                     9
% 7.54/1.53  Horn                                    13
% 7.54/1.53  unary                                   10
% 7.54/1.53  binary                                  0
% 7.54/1.53  lits                                    50
% 7.54/1.53  lits eq                                 3
% 7.54/1.53  fd_pure                                 0
% 7.54/1.53  fd_pseudo                               0
% 7.54/1.53  fd_cond                                 0
% 7.54/1.53  fd_pseudo_cond                          1
% 7.54/1.53  AC symbols                              0
% 7.54/1.53  
% 7.54/1.53  ------ Schedule dynamic 5 is on 
% 7.54/1.53  
% 7.54/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  ------ 
% 7.54/1.53  Current options:
% 7.54/1.53  ------ 
% 7.54/1.53  
% 7.54/1.53  ------ Input Options
% 7.54/1.53  
% 7.54/1.53  --out_options                           all
% 7.54/1.53  --tptp_safe_out                         true
% 7.54/1.53  --problem_path                          ""
% 7.54/1.53  --include_path                          ""
% 7.54/1.53  --clausifier                            res/vclausify_rel
% 7.54/1.53  --clausifier_options                    --mode clausify
% 7.54/1.53  --stdin                                 false
% 7.54/1.53  --stats_out                             all
% 7.54/1.53  
% 7.54/1.53  ------ General Options
% 7.54/1.53  
% 7.54/1.53  --fof                                   false
% 7.54/1.53  --time_out_real                         305.
% 7.54/1.53  --time_out_virtual                      -1.
% 7.54/1.53  --symbol_type_check                     false
% 7.54/1.53  --clausify_out                          false
% 7.54/1.53  --sig_cnt_out                           false
% 7.54/1.53  --trig_cnt_out                          false
% 7.54/1.53  --trig_cnt_out_tolerance                1.
% 7.54/1.53  --trig_cnt_out_sk_spl                   false
% 7.54/1.53  --abstr_cl_out                          false
% 7.54/1.53  
% 7.54/1.53  ------ Global Options
% 7.54/1.53  
% 7.54/1.53  --schedule                              default
% 7.54/1.53  --add_important_lit                     false
% 7.54/1.53  --prop_solver_per_cl                    1000
% 7.54/1.53  --min_unsat_core                        false
% 7.54/1.53  --soft_assumptions                      false
% 7.54/1.53  --soft_lemma_size                       3
% 7.54/1.53  --prop_impl_unit_size                   0
% 7.54/1.53  --prop_impl_unit                        []
% 7.54/1.53  --share_sel_clauses                     true
% 7.54/1.53  --reset_solvers                         false
% 7.54/1.53  --bc_imp_inh                            [conj_cone]
% 7.54/1.53  --conj_cone_tolerance                   3.
% 7.54/1.53  --extra_neg_conj                        none
% 7.54/1.53  --large_theory_mode                     true
% 7.54/1.53  --prolific_symb_bound                   200
% 7.54/1.53  --lt_threshold                          2000
% 7.54/1.53  --clause_weak_htbl                      true
% 7.54/1.53  --gc_record_bc_elim                     false
% 7.54/1.53  
% 7.54/1.53  ------ Preprocessing Options
% 7.54/1.53  
% 7.54/1.53  --preprocessing_flag                    true
% 7.54/1.53  --time_out_prep_mult                    0.1
% 7.54/1.53  --splitting_mode                        input
% 7.54/1.53  --splitting_grd                         true
% 7.54/1.53  --splitting_cvd                         false
% 7.54/1.53  --splitting_cvd_svl                     false
% 7.54/1.53  --splitting_nvd                         32
% 7.54/1.53  --sub_typing                            true
% 7.54/1.53  --prep_gs_sim                           true
% 7.54/1.53  --prep_unflatten                        true
% 7.54/1.53  --prep_res_sim                          true
% 7.54/1.53  --prep_upred                            true
% 7.54/1.53  --prep_sem_filter                       exhaustive
% 7.54/1.53  --prep_sem_filter_out                   false
% 7.54/1.53  --pred_elim                             true
% 7.54/1.53  --res_sim_input                         true
% 7.54/1.53  --eq_ax_congr_red                       true
% 7.54/1.53  --pure_diseq_elim                       true
% 7.54/1.53  --brand_transform                       false
% 7.54/1.53  --non_eq_to_eq                          false
% 7.54/1.53  --prep_def_merge                        true
% 7.54/1.53  --prep_def_merge_prop_impl              false
% 7.54/1.53  --prep_def_merge_mbd                    true
% 7.54/1.53  --prep_def_merge_tr_red                 false
% 7.54/1.53  --prep_def_merge_tr_cl                  false
% 7.54/1.53  --smt_preprocessing                     true
% 7.54/1.53  --smt_ac_axioms                         fast
% 7.54/1.53  --preprocessed_out                      false
% 7.54/1.53  --preprocessed_stats                    false
% 7.54/1.53  
% 7.54/1.53  ------ Abstraction refinement Options
% 7.54/1.53  
% 7.54/1.53  --abstr_ref                             []
% 7.54/1.53  --abstr_ref_prep                        false
% 7.54/1.53  --abstr_ref_until_sat                   false
% 7.54/1.53  --abstr_ref_sig_restrict                funpre
% 7.54/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.53  --abstr_ref_under                       []
% 7.54/1.53  
% 7.54/1.53  ------ SAT Options
% 7.54/1.53  
% 7.54/1.53  --sat_mode                              false
% 7.54/1.53  --sat_fm_restart_options                ""
% 7.54/1.53  --sat_gr_def                            false
% 7.54/1.53  --sat_epr_types                         true
% 7.54/1.53  --sat_non_cyclic_types                  false
% 7.54/1.53  --sat_finite_models                     false
% 7.54/1.53  --sat_fm_lemmas                         false
% 7.54/1.53  --sat_fm_prep                           false
% 7.54/1.53  --sat_fm_uc_incr                        true
% 7.54/1.53  --sat_out_model                         small
% 7.54/1.53  --sat_out_clauses                       false
% 7.54/1.53  
% 7.54/1.53  ------ QBF Options
% 7.54/1.53  
% 7.54/1.53  --qbf_mode                              false
% 7.54/1.53  --qbf_elim_univ                         false
% 7.54/1.53  --qbf_dom_inst                          none
% 7.54/1.53  --qbf_dom_pre_inst                      false
% 7.54/1.53  --qbf_sk_in                             false
% 7.54/1.53  --qbf_pred_elim                         true
% 7.54/1.53  --qbf_split                             512
% 7.54/1.53  
% 7.54/1.53  ------ BMC1 Options
% 7.54/1.53  
% 7.54/1.53  --bmc1_incremental                      false
% 7.54/1.53  --bmc1_axioms                           reachable_all
% 7.54/1.53  --bmc1_min_bound                        0
% 7.54/1.53  --bmc1_max_bound                        -1
% 7.54/1.53  --bmc1_max_bound_default                -1
% 7.54/1.53  --bmc1_symbol_reachability              true
% 7.54/1.53  --bmc1_property_lemmas                  false
% 7.54/1.53  --bmc1_k_induction                      false
% 7.54/1.53  --bmc1_non_equiv_states                 false
% 7.54/1.53  --bmc1_deadlock                         false
% 7.54/1.53  --bmc1_ucm                              false
% 7.54/1.53  --bmc1_add_unsat_core                   none
% 7.54/1.53  --bmc1_unsat_core_children              false
% 7.54/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.53  --bmc1_out_stat                         full
% 7.54/1.53  --bmc1_ground_init                      false
% 7.54/1.53  --bmc1_pre_inst_next_state              false
% 7.54/1.53  --bmc1_pre_inst_state                   false
% 7.54/1.53  --bmc1_pre_inst_reach_state             false
% 7.54/1.53  --bmc1_out_unsat_core                   false
% 7.54/1.53  --bmc1_aig_witness_out                  false
% 7.54/1.53  --bmc1_verbose                          false
% 7.54/1.53  --bmc1_dump_clauses_tptp                false
% 7.54/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.53  --bmc1_dump_file                        -
% 7.54/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.53  --bmc1_ucm_extend_mode                  1
% 7.54/1.53  --bmc1_ucm_init_mode                    2
% 7.54/1.53  --bmc1_ucm_cone_mode                    none
% 7.54/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.53  --bmc1_ucm_relax_model                  4
% 7.54/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.53  --bmc1_ucm_layered_model                none
% 7.54/1.53  --bmc1_ucm_max_lemma_size               10
% 7.54/1.53  
% 7.54/1.53  ------ AIG Options
% 7.54/1.53  
% 7.54/1.53  --aig_mode                              false
% 7.54/1.53  
% 7.54/1.53  ------ Instantiation Options
% 7.54/1.53  
% 7.54/1.53  --instantiation_flag                    true
% 7.54/1.53  --inst_sos_flag                         false
% 7.54/1.53  --inst_sos_phase                        true
% 7.54/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.53  --inst_lit_sel_side                     none
% 7.54/1.53  --inst_solver_per_active                1400
% 7.54/1.53  --inst_solver_calls_frac                1.
% 7.54/1.53  --inst_passive_queue_type               priority_queues
% 7.54/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.53  --inst_passive_queues_freq              [25;2]
% 7.54/1.53  --inst_dismatching                      true
% 7.54/1.53  --inst_eager_unprocessed_to_passive     true
% 7.54/1.53  --inst_prop_sim_given                   true
% 7.54/1.53  --inst_prop_sim_new                     false
% 7.54/1.53  --inst_subs_new                         false
% 7.54/1.53  --inst_eq_res_simp                      false
% 7.54/1.53  --inst_subs_given                       false
% 7.54/1.53  --inst_orphan_elimination               true
% 7.54/1.53  --inst_learning_loop_flag               true
% 7.54/1.53  --inst_learning_start                   3000
% 7.54/1.53  --inst_learning_factor                  2
% 7.54/1.53  --inst_start_prop_sim_after_learn       3
% 7.54/1.53  --inst_sel_renew                        solver
% 7.54/1.53  --inst_lit_activity_flag                true
% 7.54/1.53  --inst_restr_to_given                   false
% 7.54/1.53  --inst_activity_threshold               500
% 7.54/1.53  --inst_out_proof                        true
% 7.54/1.53  
% 7.54/1.53  ------ Resolution Options
% 7.54/1.53  
% 7.54/1.53  --resolution_flag                       false
% 7.54/1.53  --res_lit_sel                           adaptive
% 7.54/1.53  --res_lit_sel_side                      none
% 7.54/1.53  --res_ordering                          kbo
% 7.54/1.53  --res_to_prop_solver                    active
% 7.54/1.53  --res_prop_simpl_new                    false
% 7.54/1.53  --res_prop_simpl_given                  true
% 7.54/1.53  --res_passive_queue_type                priority_queues
% 7.54/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.53  --res_passive_queues_freq               [15;5]
% 7.54/1.53  --res_forward_subs                      full
% 7.54/1.53  --res_backward_subs                     full
% 7.54/1.53  --res_forward_subs_resolution           true
% 7.54/1.53  --res_backward_subs_resolution          true
% 7.54/1.53  --res_orphan_elimination                true
% 7.54/1.53  --res_time_limit                        2.
% 7.54/1.53  --res_out_proof                         true
% 7.54/1.53  
% 7.54/1.53  ------ Superposition Options
% 7.54/1.53  
% 7.54/1.53  --superposition_flag                    true
% 7.54/1.53  --sup_passive_queue_type                priority_queues
% 7.54/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.53  --demod_completeness_check              fast
% 7.54/1.53  --demod_use_ground                      true
% 7.54/1.53  --sup_to_prop_solver                    passive
% 7.54/1.53  --sup_prop_simpl_new                    true
% 7.54/1.53  --sup_prop_simpl_given                  true
% 7.54/1.53  --sup_fun_splitting                     false
% 7.54/1.53  --sup_smt_interval                      50000
% 7.54/1.53  
% 7.54/1.53  ------ Superposition Simplification Setup
% 7.54/1.53  
% 7.54/1.53  --sup_indices_passive                   []
% 7.54/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_full_bw                           [BwDemod]
% 7.54/1.53  --sup_immed_triv                        [TrivRules]
% 7.54/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_immed_bw_main                     []
% 7.54/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.53  
% 7.54/1.53  ------ Combination Options
% 7.54/1.53  
% 7.54/1.53  --comb_res_mult                         3
% 7.54/1.53  --comb_sup_mult                         2
% 7.54/1.53  --comb_inst_mult                        10
% 7.54/1.53  
% 7.54/1.53  ------ Debug Options
% 7.54/1.53  
% 7.54/1.53  --dbg_backtrace                         false
% 7.54/1.53  --dbg_dump_prop_clauses                 false
% 7.54/1.53  --dbg_dump_prop_clauses_file            -
% 7.54/1.53  --dbg_out_stat                          false
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  ------ Proving...
% 7.54/1.53  
% 7.54/1.53  
% 7.54/1.53  % SZS status Theorem for theBenchmark.p
% 7.54/1.53  
% 7.54/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.53  
% 7.54/1.53  fof(f5,conjecture,(
% 7.54/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.54/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.53  
% 7.54/1.53  fof(f6,negated_conjecture,(
% 7.54/1.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 7.54/1.53    inference(negated_conjecture,[],[f5])).
% 7.54/1.53  
% 7.54/1.53  fof(f15,plain,(
% 7.54/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.54/1.53    inference(ennf_transformation,[],[f6])).
% 7.54/1.53  
% 7.54/1.53  fof(f16,plain,(
% 7.54/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.54/1.53    inference(flattening,[],[f15])).
% 7.54/1.53  
% 7.54/1.53  fof(f22,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.54/1.53    introduced(choice_axiom,[])).
% 7.54/1.53  
% 7.54/1.53  fof(f21,plain,(
% 7.54/1.53    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.54/1.53    introduced(choice_axiom,[])).
% 7.54/1.53  
% 7.54/1.53  fof(f20,plain,(
% 7.54/1.53    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 7.54/1.53    introduced(choice_axiom,[])).
% 7.54/1.53  
% 7.54/1.53  fof(f19,plain,(
% 7.54/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.54/1.53    introduced(choice_axiom,[])).
% 7.54/1.53  
% 7.54/1.53  fof(f23,plain,(
% 7.54/1.53    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.54/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22,f21,f20,f19])).
% 7.54/1.53  
% 7.54/1.53  fof(f40,plain,(
% 7.54/1.53    m1_pre_topc(sK3,sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f36,plain,(
% 7.54/1.53    m1_pre_topc(sK1,sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f2,axiom,(
% 7.54/1.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 7.54/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.53  
% 7.54/1.53  fof(f9,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.53    inference(ennf_transformation,[],[f2])).
% 7.54/1.53  
% 7.54/1.53  fof(f10,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.53    inference(flattening,[],[f9])).
% 7.54/1.53  
% 7.54/1.53  fof(f17,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.53    inference(nnf_transformation,[],[f10])).
% 7.54/1.53  
% 7.54/1.53  fof(f25,plain,(
% 7.54/1.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f17])).
% 7.54/1.53  
% 7.54/1.53  fof(f44,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.53    inference(equality_resolution,[],[f25])).
% 7.54/1.53  
% 7.54/1.53  fof(f3,axiom,(
% 7.54/1.53    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.54/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.53  
% 7.54/1.53  fof(f11,plain,(
% 7.54/1.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.53    inference(ennf_transformation,[],[f3])).
% 7.54/1.53  
% 7.54/1.53  fof(f12,plain,(
% 7.54/1.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.53    inference(flattening,[],[f11])).
% 7.54/1.53  
% 7.54/1.53  fof(f27,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f12])).
% 7.54/1.53  
% 7.54/1.53  fof(f28,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f12])).
% 7.54/1.53  
% 7.54/1.53  fof(f29,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f12])).
% 7.54/1.53  
% 7.54/1.53  fof(f34,plain,(
% 7.54/1.53    l1_pre_topc(sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f32,plain,(
% 7.54/1.53    ~v2_struct_0(sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f35,plain,(
% 7.54/1.53    ~v2_struct_0(sK1)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f39,plain,(
% 7.54/1.53    ~v2_struct_0(sK3)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f1,axiom,(
% 7.54/1.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.54/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.53  
% 7.54/1.53  fof(f7,plain,(
% 7.54/1.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.54/1.53    inference(ennf_transformation,[],[f1])).
% 7.54/1.53  
% 7.54/1.53  fof(f8,plain,(
% 7.54/1.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.54/1.53    inference(flattening,[],[f7])).
% 7.54/1.53  
% 7.54/1.53  fof(f24,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f8])).
% 7.54/1.53  
% 7.54/1.53  fof(f4,axiom,(
% 7.54/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.54/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.53  
% 7.54/1.53  fof(f13,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.54/1.53    inference(ennf_transformation,[],[f4])).
% 7.54/1.53  
% 7.54/1.53  fof(f14,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.54/1.53    inference(flattening,[],[f13])).
% 7.54/1.53  
% 7.54/1.53  fof(f18,plain,(
% 7.54/1.53    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.54/1.53    inference(nnf_transformation,[],[f14])).
% 7.54/1.53  
% 7.54/1.53  fof(f30,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f18])).
% 7.54/1.53  
% 7.54/1.53  fof(f33,plain,(
% 7.54/1.53    v2_pre_topc(sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f43,plain,(
% 7.54/1.53    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f31,plain,(
% 7.54/1.53    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.54/1.53    inference(cnf_transformation,[],[f18])).
% 7.54/1.53  
% 7.54/1.53  fof(f42,plain,(
% 7.54/1.53    m1_pre_topc(sK3,sK2)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f41,plain,(
% 7.54/1.53    m1_pre_topc(sK1,sK2)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  fof(f38,plain,(
% 7.54/1.53    m1_pre_topc(sK2,sK0)),
% 7.54/1.53    inference(cnf_transformation,[],[f23])).
% 7.54/1.53  
% 7.54/1.53  cnf(c_11,negated_conjecture,
% 7.54/1.53      ( m1_pre_topc(sK3,sK0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f40]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_726,negated_conjecture,
% 7.54/1.53      ( m1_pre_topc(sK3,sK0) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_11]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1067,plain,
% 7.54/1.53      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_15,negated_conjecture,
% 7.54/1.53      ( m1_pre_topc(sK1,sK0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f36]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_722,negated_conjecture,
% 7.54/1.53      ( m1_pre_topc(sK1,sK0) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_15]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1071,plain,
% 7.54/1.53      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_2,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 7.54/1.53      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 7.54/1.53      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 7.54/1.53      inference(cnf_transformation,[],[f44]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_5,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 7.54/1.53      inference(cnf_transformation,[],[f27]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_4,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
% 7.54/1.53      inference(cnf_transformation,[],[f28]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f29]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_112,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_2,c_5,c_4,c_3]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_113,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_112]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_17,negated_conjecture,
% 7.54/1.53      ( l1_pre_topc(sK0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f34]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_322,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
% 7.54/1.53      | sK0 != X1 ),
% 7.54/1.53      inference(resolution_lifted,[status(thm)],[c_113,c_17]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_323,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(sK0)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.54/1.53      inference(unflattening,[status(thm)],[c_322]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_19,negated_conjecture,
% 7.54/1.53      ( ~ v2_struct_0(sK0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f32]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_327,plain,
% 7.54/1.53      ( v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_323,c_19]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_328,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_327]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_717,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1_41,sK0)
% 7.54/1.53      | v2_struct_0(X1_41)
% 7.54/1.53      | v2_struct_0(X0_41)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,X0_41,X1_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_328]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1076,plain,
% 7.54/1.53      ( u1_struct_0(k1_tsep_1(sK0,X0_41,X1_41)) = k2_xboole_0(u1_struct_0(X0_41),u1_struct_0(X1_41))
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | m1_pre_topc(X1_41,sK0) != iProver_top
% 7.54/1.53      | v2_struct_0(X1_41) = iProver_top
% 7.54/1.53      | v2_struct_0(X0_41) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_2782,plain,
% 7.54/1.53      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41))
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | v2_struct_0(X0_41) = iProver_top
% 7.54/1.53      | v2_struct_0(sK1) = iProver_top ),
% 7.54/1.53      inference(superposition,[status(thm)],[c_1071,c_1076]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_16,negated_conjecture,
% 7.54/1.53      ( ~ v2_struct_0(sK1) ),
% 7.54/1.53      inference(cnf_transformation,[],[f35]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_23,plain,
% 7.54/1.53      ( v2_struct_0(sK1) != iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3678,plain,
% 7.54/1.53      ( v2_struct_0(X0_41) = iProver_top
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_2782,c_23]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3679,plain,
% 7.54/1.53      ( u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41))
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | v2_struct_0(X0_41) = iProver_top ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_3678]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3687,plain,
% 7.54/1.53      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
% 7.54/1.53      | v2_struct_0(sK3) = iProver_top ),
% 7.54/1.53      inference(superposition,[status(thm)],[c_1067,c_3679]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_12,negated_conjecture,
% 7.54/1.53      ( ~ v2_struct_0(sK3) ),
% 7.54/1.53      inference(cnf_transformation,[],[f39]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1304,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.53      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.53      | v2_struct_0(X0_41)
% 7.54/1.53      | v2_struct_0(sK1)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,sK1,X0_41)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
% 7.54/1.53      inference(instantiation,[status(thm)],[c_717]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1570,plain,
% 7.54/1.53      ( ~ m1_pre_topc(sK3,sK0)
% 7.54/1.53      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.53      | v2_struct_0(sK3)
% 7.54/1.53      | v2_struct_0(sK1)
% 7.54/1.53      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.54/1.53      inference(instantiation,[status(thm)],[c_1304]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3928,plain,
% 7.54/1.53      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_3687,c_16,c_15,c_12,c_11,c_1570]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_0,plain,
% 7.54/1.53      ( ~ r1_tarski(X0,X1)
% 7.54/1.53      | ~ r1_tarski(X2,X1)
% 7.54/1.53      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 7.54/1.53      inference(cnf_transformation,[],[f24]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_730,plain,
% 7.54/1.53      ( ~ r1_tarski(X0_42,X1_42)
% 7.54/1.53      | ~ r1_tarski(X2_42,X1_42)
% 7.54/1.53      | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_0]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1063,plain,
% 7.54/1.53      ( r1_tarski(X0_42,X1_42) != iProver_top
% 7.54/1.53      | r1_tarski(X2_42,X1_42) != iProver_top
% 7.54/1.53      | r1_tarski(k2_xboole_0(X2_42,X0_42),X1_42) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_3932,plain,
% 7.54/1.53      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),X0_42) = iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK3),X0_42) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK1),X0_42) != iProver_top ),
% 7.54/1.53      inference(superposition,[status(thm)],[c_3928,c_1063]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_7,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | m1_pre_topc(X2,X0)
% 7.54/1.53      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.54/1.53      | ~ v2_pre_topc(X1)
% 7.54/1.53      | ~ l1_pre_topc(X1) ),
% 7.54/1.53      inference(cnf_transformation,[],[f30]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_18,negated_conjecture,
% 7.54/1.53      ( v2_pre_topc(sK0) ),
% 7.54/1.53      inference(cnf_transformation,[],[f33]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_212,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | m1_pre_topc(X2,X0)
% 7.54/1.53      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.54/1.53      | ~ l1_pre_topc(X1)
% 7.54/1.53      | sK0 != X1 ),
% 7.54/1.53      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_213,plain,
% 7.54/1.53      ( m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.53      | ~ l1_pre_topc(sK0) ),
% 7.54/1.53      inference(unflattening,[status(thm)],[c_212]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_215,plain,
% 7.54/1.53      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | m1_pre_topc(X0,X1) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_213,c_17]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_216,plain,
% 7.54/1.53      ( m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_215]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_719,plain,
% 7.54/1.53      ( m1_pre_topc(X0_41,X1_41)
% 7.54/1.53      | ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1_41,sK0)
% 7.54/1.53      | ~ r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_216]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1074,plain,
% 7.54/1.53      ( m1_pre_topc(X0_41,X1_41) = iProver_top
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | m1_pre_topc(X1_41,sK0) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) != iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_4933,plain,
% 7.54/1.53      ( m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
% 7.54/1.53      inference(superposition,[status(thm)],[c_3932,c_1074]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_24,plain,
% 7.54/1.53      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_27,plain,
% 7.54/1.53      ( v2_struct_0(sK3) != iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_28,plain,
% 7.54/1.53      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_397,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X2)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | sK0 != X1 ),
% 7.54/1.53      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_398,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(sK0) ),
% 7.54/1.53      inference(unflattening,[status(thm)],[c_397]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_402,plain,
% 7.54/1.53      ( v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X1)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_398,c_19]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_403,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.54/1.53      | v2_struct_0(X0)
% 7.54/1.53      | v2_struct_0(X1) ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_402]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_714,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1_41,sK0)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,X0_41,X1_41),sK0)
% 7.54/1.53      | v2_struct_0(X1_41)
% 7.54/1.53      | v2_struct_0(X0_41) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_403]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1235,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_41),sK0)
% 7.54/1.53      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.53      | v2_struct_0(X0_41)
% 7.54/1.53      | v2_struct_0(sK1) ),
% 7.54/1.53      inference(instantiation,[status(thm)],[c_714]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1422,plain,
% 7.54/1.53      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 7.54/1.53      | ~ m1_pre_topc(sK3,sK0)
% 7.54/1.53      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.53      | v2_struct_0(sK3)
% 7.54/1.53      | v2_struct_0(sK1) ),
% 7.54/1.53      inference(instantiation,[status(thm)],[c_1235]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1423,plain,
% 7.54/1.53      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 7.54/1.53      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.54/1.53      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.54/1.53      | v2_struct_0(sK3) = iProver_top
% 7.54/1.53      | v2_struct_0(sK1) = iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_19645,plain,
% 7.54/1.53      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
% 7.54/1.53      | m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_4933,c_23,c_24,c_27,c_28,c_1423]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_19646,plain,
% 7.54/1.53      ( m1_pre_topc(X0_41,sK0) != iProver_top
% 7.54/1.53      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0_41) = iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) != iProver_top ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_19645]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_8,negated_conjecture,
% 7.54/1.53      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 7.54/1.53      inference(cnf_transformation,[],[f43]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_729,negated_conjecture,
% 7.54/1.53      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 7.54/1.53      inference(subtyping,[status(esa)],[c_8]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_1064,plain,
% 7.54/1.53      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
% 7.54/1.53      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_19655,plain,
% 7.54/1.53      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.54/1.53      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.53      inference(superposition,[status(thm)],[c_19646,c_1064]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_6,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X1)
% 7.54/1.53      | ~ m1_pre_topc(X2,X0)
% 7.54/1.53      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.54/1.53      | ~ v2_pre_topc(X1)
% 7.54/1.53      | ~ l1_pre_topc(X1) ),
% 7.54/1.53      inference(cnf_transformation,[],[f31]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_232,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X1,X2)
% 7.54/1.53      | ~ m1_pre_topc(X0,X2)
% 7.54/1.53      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.53      | ~ l1_pre_topc(X2)
% 7.54/1.53      | sK0 != X2 ),
% 7.54/1.53      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_233,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.53      | ~ l1_pre_topc(sK0) ),
% 7.54/1.53      inference(unflattening,[status(thm)],[c_232]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_237,plain,
% 7.54/1.53      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X0,X1) ),
% 7.54/1.53      inference(global_propositional_subsumption,
% 7.54/1.53                [status(thm)],
% 7.54/1.53                [c_233,c_17]) ).
% 7.54/1.53  
% 7.54/1.53  cnf(c_238,plain,
% 7.54/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.53      | ~ m1_pre_topc(X0,sK0)
% 7.54/1.53      | ~ m1_pre_topc(X1,sK0)
% 7.54/1.53      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.54/1.53      inference(renaming,[status(thm)],[c_237]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_718,plain,
% 7.54/1.54      ( ~ m1_pre_topc(X0_41,X1_41)
% 7.54/1.54      | ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.54      | ~ m1_pre_topc(X1_41,sK0)
% 7.54/1.54      | r1_tarski(u1_struct_0(X0_41),u1_struct_0(X1_41)) ),
% 7.54/1.54      inference(subtyping,[status(esa)],[c_238]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1280,plain,
% 7.54/1.54      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.54      | ~ m1_pre_topc(sK1,X0_41)
% 7.54/1.54      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.54      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0_41)) ),
% 7.54/1.54      inference(instantiation,[status(thm)],[c_718]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1528,plain,
% 7.54/1.54      ( ~ m1_pre_topc(sK2,sK0)
% 7.54/1.54      | ~ m1_pre_topc(sK1,sK2)
% 7.54/1.54      | ~ m1_pre_topc(sK1,sK0)
% 7.54/1.54      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.54/1.54      inference(instantiation,[status(thm)],[c_1280]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1529,plain,
% 7.54/1.54      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.54/1.54      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.54/1.54      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.54/1.54      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.54      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1270,plain,
% 7.54/1.54      ( ~ m1_pre_topc(X0_41,sK0)
% 7.54/1.54      | ~ m1_pre_topc(sK3,X0_41)
% 7.54/1.54      | ~ m1_pre_topc(sK3,sK0)
% 7.54/1.54      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_41)) ),
% 7.54/1.54      inference(instantiation,[status(thm)],[c_718]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1510,plain,
% 7.54/1.54      ( ~ m1_pre_topc(sK2,sK0)
% 7.54/1.54      | ~ m1_pre_topc(sK3,sK2)
% 7.54/1.54      | ~ m1_pre_topc(sK3,sK0)
% 7.54/1.54      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 7.54/1.54      inference(instantiation,[status(thm)],[c_1270]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_1511,plain,
% 7.54/1.54      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.54/1.54      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.54/1.54      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.54/1.54      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.54      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_9,negated_conjecture,
% 7.54/1.54      ( m1_pre_topc(sK3,sK2) ),
% 7.54/1.54      inference(cnf_transformation,[],[f42]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_30,plain,
% 7.54/1.54      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.54/1.54      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_10,negated_conjecture,
% 7.54/1.54      ( m1_pre_topc(sK1,sK2) ),
% 7.54/1.54      inference(cnf_transformation,[],[f41]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_29,plain,
% 7.54/1.54      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.54/1.54      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_13,negated_conjecture,
% 7.54/1.54      ( m1_pre_topc(sK2,sK0) ),
% 7.54/1.54      inference(cnf_transformation,[],[f38]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(c_26,plain,
% 7.54/1.54      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.54/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.54/1.54  
% 7.54/1.54  cnf(contradiction,plain,
% 7.54/1.54      ( $false ),
% 7.54/1.54      inference(minisat,
% 7.54/1.54                [status(thm)],
% 7.54/1.54                [c_19655,c_1529,c_1511,c_30,c_29,c_28,c_26,c_24]) ).
% 7.54/1.54  
% 7.54/1.54  
% 7.54/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.54  
% 7.54/1.54  ------                               Statistics
% 7.54/1.54  
% 7.54/1.54  ------ General
% 7.54/1.54  
% 7.54/1.54  abstr_ref_over_cycles:                  0
% 7.54/1.54  abstr_ref_under_cycles:                 0
% 7.54/1.54  gc_basic_clause_elim:                   0
% 7.54/1.54  forced_gc_time:                         0
% 7.54/1.54  parsing_time:                           0.01
% 7.54/1.54  unif_index_cands_time:                  0.
% 7.54/1.54  unif_index_add_time:                    0.
% 7.54/1.54  orderings_time:                         0.
% 7.54/1.54  out_proof_time:                         0.01
% 7.54/1.54  total_time:                             0.59
% 7.54/1.54  num_of_symbols:                         46
% 7.54/1.54  num_of_terms:                           20054
% 7.54/1.54  
% 7.54/1.54  ------ Preprocessing
% 7.54/1.54  
% 7.54/1.54  num_of_splits:                          0
% 7.54/1.54  num_of_split_atoms:                     0
% 7.54/1.54  num_of_reused_defs:                     0
% 7.54/1.54  num_eq_ax_congr_red:                    0
% 7.54/1.54  num_of_sem_filtered_clauses:            1
% 7.54/1.54  num_of_subtypes:                        2
% 7.54/1.54  monotx_restored_types:                  0
% 7.54/1.54  sat_num_of_epr_types:                   0
% 7.54/1.54  sat_num_of_non_cyclic_types:            0
% 7.54/1.54  sat_guarded_non_collapsed_types:        1
% 7.54/1.54  num_pure_diseq_elim:                    0
% 7.54/1.54  simp_replaced_by:                       0
% 7.54/1.54  res_preprocessed:                       97
% 7.54/1.54  prep_upred:                             0
% 7.54/1.54  prep_unflattend:                        10
% 7.54/1.54  smt_new_axioms:                         0
% 7.54/1.54  pred_elim_cands:                        4
% 7.54/1.54  pred_elim:                              2
% 7.54/1.54  pred_elim_cl:                           2
% 7.54/1.54  pred_elim_cycles:                       5
% 7.54/1.54  merged_defs:                            0
% 7.54/1.54  merged_defs_ncl:                        0
% 7.54/1.54  bin_hyper_res:                          0
% 7.54/1.54  prep_cycles:                            4
% 7.54/1.54  pred_elim_time:                         0.01
% 7.54/1.54  splitting_time:                         0.
% 7.54/1.54  sem_filter_time:                        0.
% 7.54/1.54  monotx_time:                            0.
% 7.54/1.54  subtype_inf_time:                       0.
% 7.54/1.54  
% 7.54/1.54  ------ Problem properties
% 7.54/1.54  
% 7.54/1.54  clauses:                                18
% 7.54/1.54  conjectures:                            10
% 7.54/1.54  epr:                                    9
% 7.54/1.54  horn:                                   13
% 7.54/1.54  ground:                                 10
% 7.54/1.54  unary:                                  10
% 7.54/1.54  binary:                                 0
% 7.54/1.54  lits:                                   50
% 7.54/1.54  lits_eq:                                3
% 7.54/1.54  fd_pure:                                0
% 7.54/1.54  fd_pseudo:                              0
% 7.54/1.54  fd_cond:                                0
% 7.54/1.54  fd_pseudo_cond:                         1
% 7.54/1.54  ac_symbols:                             0
% 7.54/1.54  
% 7.54/1.54  ------ Propositional Solver
% 7.54/1.54  
% 7.54/1.54  prop_solver_calls:                      28
% 7.54/1.54  prop_fast_solver_calls:                 1543
% 7.54/1.54  smt_solver_calls:                       0
% 7.54/1.54  smt_fast_solver_calls:                  0
% 7.54/1.54  prop_num_of_clauses:                    6252
% 7.54/1.54  prop_preprocess_simplified:             11195
% 7.54/1.54  prop_fo_subsumed:                       144
% 7.54/1.54  prop_solver_time:                       0.
% 7.54/1.54  smt_solver_time:                        0.
% 7.54/1.54  smt_fast_solver_time:                   0.
% 7.54/1.54  prop_fast_solver_time:                  0.
% 7.54/1.54  prop_unsat_core_time:                   0.
% 7.54/1.54  
% 7.54/1.54  ------ QBF
% 7.54/1.54  
% 7.54/1.54  qbf_q_res:                              0
% 7.54/1.54  qbf_num_tautologies:                    0
% 7.54/1.54  qbf_prep_cycles:                        0
% 7.54/1.54  
% 7.54/1.54  ------ BMC1
% 7.54/1.54  
% 7.54/1.54  bmc1_current_bound:                     -1
% 7.54/1.54  bmc1_last_solved_bound:                 -1
% 7.54/1.54  bmc1_unsat_core_size:                   -1
% 7.54/1.54  bmc1_unsat_core_parents_size:           -1
% 7.54/1.54  bmc1_merge_next_fun:                    0
% 7.54/1.54  bmc1_unsat_core_clauses_time:           0.
% 7.54/1.54  
% 7.54/1.54  ------ Instantiation
% 7.54/1.54  
% 7.54/1.54  inst_num_of_clauses:                    1463
% 7.54/1.54  inst_num_in_passive:                    257
% 7.54/1.54  inst_num_in_active:                     915
% 7.54/1.54  inst_num_in_unprocessed:                291
% 7.54/1.54  inst_num_of_loops:                      960
% 7.54/1.54  inst_num_of_learning_restarts:          0
% 7.54/1.54  inst_num_moves_active_passive:          44
% 7.54/1.54  inst_lit_activity:                      0
% 7.54/1.54  inst_lit_activity_moves:                1
% 7.54/1.54  inst_num_tautologies:                   0
% 7.54/1.54  inst_num_prop_implied:                  0
% 7.54/1.54  inst_num_existing_simplified:           0
% 7.54/1.54  inst_num_eq_res_simplified:             0
% 7.54/1.54  inst_num_child_elim:                    0
% 7.54/1.54  inst_num_of_dismatching_blockings:      3487
% 7.54/1.54  inst_num_of_non_proper_insts:           1430
% 7.54/1.54  inst_num_of_duplicates:                 0
% 7.54/1.54  inst_inst_num_from_inst_to_res:         0
% 7.54/1.54  inst_dismatching_checking_time:         0.
% 7.54/1.54  
% 7.54/1.54  ------ Resolution
% 7.54/1.54  
% 7.54/1.54  res_num_of_clauses:                     0
% 7.54/1.54  res_num_in_passive:                     0
% 7.54/1.54  res_num_in_active:                      0
% 7.54/1.54  res_num_of_loops:                       101
% 7.54/1.54  res_forward_subset_subsumed:            19
% 7.54/1.54  res_backward_subset_subsumed:           0
% 7.54/1.54  res_forward_subsumed:                   0
% 7.54/1.54  res_backward_subsumed:                  0
% 7.54/1.54  res_forward_subsumption_resolution:     5
% 7.54/1.54  res_backward_subsumption_resolution:    0
% 7.54/1.54  res_clause_to_clause_subsumption:       2859
% 7.54/1.54  res_orphan_elimination:                 0
% 7.54/1.54  res_tautology_del:                      89
% 7.54/1.54  res_num_eq_res_simplified:              0
% 7.54/1.54  res_num_sel_changes:                    0
% 7.54/1.54  res_moves_from_active_to_pass:          0
% 7.54/1.54  
% 7.54/1.54  ------ Superposition
% 7.54/1.54  
% 7.54/1.54  sup_time_total:                         0.
% 7.54/1.54  sup_time_generating:                    0.
% 7.54/1.54  sup_time_sim_full:                      0.
% 7.54/1.54  sup_time_sim_immed:                     0.
% 7.54/1.54  
% 7.54/1.54  sup_num_of_clauses:                     546
% 7.54/1.54  sup_num_in_active:                      191
% 7.54/1.54  sup_num_in_passive:                     355
% 7.54/1.54  sup_num_of_loops:                       190
% 7.54/1.54  sup_fw_superposition:                   296
% 7.54/1.54  sup_bw_superposition:                   274
% 7.54/1.54  sup_immediate_simplified:               0
% 7.54/1.54  sup_given_eliminated:                   0
% 7.54/1.54  comparisons_done:                       0
% 7.54/1.54  comparisons_avoided:                    0
% 7.54/1.54  
% 7.54/1.54  ------ Simplifications
% 7.54/1.54  
% 7.54/1.54  
% 7.54/1.54  sim_fw_subset_subsumed:                 3
% 7.54/1.54  sim_bw_subset_subsumed:                 21
% 7.54/1.54  sim_fw_subsumed:                        1
% 7.54/1.54  sim_bw_subsumed:                        0
% 7.54/1.54  sim_fw_subsumption_res:                 0
% 7.54/1.54  sim_bw_subsumption_res:                 0
% 7.54/1.54  sim_tautology_del:                      1
% 7.54/1.54  sim_eq_tautology_del:                   0
% 7.54/1.54  sim_eq_res_simp:                        0
% 7.54/1.54  sim_fw_demodulated:                     0
% 7.54/1.54  sim_bw_demodulated:                     0
% 7.54/1.54  sim_light_normalised:                   0
% 7.54/1.54  sim_joinable_taut:                      0
% 7.54/1.54  sim_joinable_simp:                      0
% 7.54/1.54  sim_ac_normalised:                      0
% 7.54/1.54  sim_smt_subsumption:                    0
% 7.54/1.54  
%------------------------------------------------------------------------------
